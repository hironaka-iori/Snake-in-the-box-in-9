"""Apply the round-222 revision to the existing editor sources and exact mirrors."""
from pathlib import Path
import hashlib
import json
import re

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
EDITOR = Path('D:/Codex/2026-10-13/new-chat/outputs')

def sha(data):
    return hashlib.sha256(data).hexdigest()

def once(text, old, new):
    if text.count(old) != 1:
        raise RuntimeError('Expected exactly one source passage: ' + old[:100])
    return text.replace(old, new, 1)

required = {
    'prefix-audit.json': 'PASS_EXACT_STAGE1_PREFIX_COVERAGE_AND_CERTIFICATES',
    'deep-audit.json': 'PASS_EXACT_COMPLETE_FIXED_ROOT_PREFIX_EXCLUSION',
    'Prefix222-audit.json': 'PASS',
    'PartnerIsometry222-audit.json': 'PASS',
}
audit_pins = {}
for name, status in required.items():
    path = H / 'data' / name
    raw = path.read_bytes()
    if json.loads(raw)['status'] != status:
        raise RuntimeError('Required accepted evidence is absent: ' + name)
    audit_pins[name] = sha(raw)

names = ['snake9_research.tex', 'snake9_frontier_explanation.tex']
before = {name: (H / 'data' / ('before-' + name)).read_bytes() for name in names}
expected_before = {
    'snake9_research.tex': '09a30206191809ba80a7d6ee11af6fcd3fb99e589d84243f970da182a8a170bf',
    'snake9_frontier_explanation.tex': 'adbac0716c6ee01d61f2b801e4809d10f19e69c0ee80c04da728378df860873d',
}
for name in names:
    if sha(before[name]) != expected_before[name]:
        raise RuntimeError('Unexpected original snapshot: ' + name)

main = before[names[0]].decode('utf-8')
main = once(main, r'\date{Research state after round 221, 15 November 2026}',
            r'\date{Research state after round 222, 15 November 2026}')
main = once(main, r'''Exact certificates exclude a 95-edge compatible partner at either
endpoint of the saved 98-edge parent. Its one-crossing construction
therefore has at most 193 edges. The 93-edge partner needed for 192
remains unresolved. Exact fractional points satisfy the degree and
linear product constraints together with every cycle occupancy,
subset forest and disagreement-cycle parity inequality at total weight
94. Fixing an actual first step excludes three of fourteen branches;
the other eleven remain open.''', r'''Complete prefix coverage and exact certificates exclude every 93-edge
compatible partner at either endpoint of the saved 98-edge parent.
Any longer partner would contain such a prefix, so arbitrary compatible
partners have at most 92 edges. A one-crossing join using this parent,
or any cube-isometric copy, consequently has at most 191 edges.
This ceiling is not an attainment claim. The unconditioned continuous
model still has exact fractional points of weight 94 satisfying all
cycle occupancy, subset forest and disagreement-cycle parity inequalities.
The exclusion uses a complete finite division into actual path prefixes.
Generic Lean implications and independent exact numerical certificates
have separate verification records.''')
main = once(main, r'''\label{sec:parity221}
Every closed Boolean walk''', r'''\label{sec:parity221}
This subsection records the round-221 comparison. The stronger prefix
exclusion in Section~\ref{sec:prefix222} resolves its remaining branches.
Every closed Boolean walk''')
main = once(main, r'''The other eleven remain unresolved: their upper bounds alone do not
prove feasibility. Extending these remaining prefixes is a concrete
next step. All certificates and scope records are retained in
milestone 221~\cite{research221}.''', r'''At this stage the other eleven were unresolved: their upper bounds alone
did not prove feasibility. Section~\ref{sec:prefix222} completes their
prefix division. The first-step certificates and their scope records
remain in milestone 221~\cite{research221}.''')

prefix_section = r'''\subsection{Complete prefix exclusion for the saved parent}
\label{sec:prefix222}
Let $P$ be the specified 98-edge parent and let $t\in\{0,78\}$ be its
joining endpoint. Compatibility requires an induced partner beginning
at $t$ and avoiding every vertex of $P$ except $t$. The permitted graph
therefore remains $Q_8\setminus(V(P)\setminus\{t\})$; no neighbour of
a parent vertex is additionally forbidden.

\paragraph{Necessary rows and complete continuation.}
Suppose $q_0,\ldots,q_{93}$ were a compatible 93-edge path. At a proper
prefix $q_0,\ldots,q_k$, with $k<93$, the selection and free-endpoint
indicators satisfy
\[
x_{q_i}=1\quad(0\le i\le k),\qquad
e_{q_i}=0\quad(0<i\le k).
\]
Injectivity excludes equality of these nonroot prefix vertices with
either full-path endpoint. In particular, the current last prefix vertex
is still internal to the complete path. The endpoint equality is imposed
where that variable exists; even vertices already have endpoint value zero.

The next vertex must be allowed, adjacent to $q_k$, distinct from every
prefix vertex, and nonadjacent to $q_i$ for $i<k$. Injectivity and
inducedness give these restrictions directly. Enumerating every allowed
vertex satisfying them therefore covers every possible next step.
The restrictions are necessary; an enumerated child need not have a completion.
Each branch retains the fixed model and adds its proper-prefix equalities.
An exact weighted-row cardinality bound below 94 excludes that branch.
Every remaining branch is divided into all of its induced next-step children.

\paragraph{The complete finite cover.}
The resulting tree has the following counts, with depth measured in prefix edges:
\[
\begin{array}{c|r|r|r}
\text{Depth}&\text{Nodes}&\text{Excluded}&\text{Expanded}\\\hline
1&14&3&11\\
2&33&23&10\\
3&21&17&4\\
4&9&8&1\\
5&1&0&1\\
6&2&2&0\\\hline
\text{Total}&80&53&27
\end{array}
\]
No leaf remains pending. There are 31 excluded leaves at root 0 and 22
at root 78. Their largest exact cardinality bounds are respectively
93.963070 and 93.984077, both strictly below 94.
The unique prefix surviving depth four was
\[
(78,206,198,196,197).
\]
Its only allowed next vertex is 213, after which the only possibilities
are 215 and 221. The two depth-six certificates give exact bounds
93.979475 and 93.414818, respectively.

The original native batch stopped for low free memory after 45 completed
new queries. Its three inherited exclusions and all completed records
were retained, with 20 queued prefixes saved for continuation. The resumed
and deeper calculations completed the cover. The interruption remains
recorded as an interrupted run; successful individual certificates are
supported by their independent arithmetic audits.

\begin{proposition}[One-crossing ceiling for the saved parent class]
\label{prop:parent191}
For the specified 98-edge parent, or any cube-isometric copy, every
compatible induced partner beginning at either endpoint has at most
92 edges. A one-crossing join using the entire parent therefore has
at most 191 edges.
\end{proposition}
\begin{proof}
Every hypothetical 93-edge partner begins in one of the fourteen
first-step branches. At each expanded prefix, its next vertex belongs
to the complete child list. It must consequently reach an excluded leaf
at depth at most six. Since $6<93$, all prefix nonendpoint equalities
used there are valid. Its Boolean assignment would have 94 selected
vertices, contradicting that leaf's exact upper bound below 94.
Any longer compatible partner contains a compatible 93-edge prefix,
so arbitrary partner length is at most 92. The joining length is then
at most $98+92+1=191$.

If a cube isometry sends the parent to another copy, apply its inverse
to a hypothetical partner for that copy. The inverse preserves inducedness,
length, the designated joining endpoint and avoidance of all other parent
vertices. It would therefore produce a forbidden partner for the original
parent. The same bound holds throughout this cube-isometry class.
\end{proof}

Independent exact audits reconstruct the finite child cover, prefix rows
and weighted-row certificates; a separate mathematical review verifies
that every actual compatible path satisfies the model. Two Lean modules
check four generic results covering proper-prefix continuation, nonendpoint
facts and the isometry pullback. The complete numerical tree and coefficient
arrays have no end-to-end Lean assembly. All records, including the resource
interruption, are retained in milestone 222~\cite{research222}.

No compatible 92-edge witness or attainment of this 191-edge ceiling is
established. The result excludes improvement by a one-crossing join using
this full parent class. Different parent classes, shorter parents and
constructions with multiple crossings remain outside its scope.
The exact fractional weight-94 points of Section~\ref{sec:parity221}
remain valid in the unconditioned relaxation: splitting into actual
prefixes adds restrictions that those fractional points need not satisfy.
The global interval $191\le a(9)\le233$ is unchanged.

'''
main = once(main, r'\section{Verification scope and remaining problem}\label{sec:verification}',
            prefix_section + r'\section{Verification scope and remaining problem}\label{sec:verification}')
main = once(main, r'''For the fixed 98-edge parent, exact parity-strengthened certificates
exclude a 95-edge partner at either endpoint, giving a one-crossing
ceiling of 193. The 93-edge targets remain open. Exact fractional
assignments satisfy every occupancy-cycle, subset-forest and
disagreement-cycle parity inequality at total weight 94. Requiring an
actual first step excludes three of fourteen branches. The corresponding
generic Lean results, exact finite audits and the remaining Lean
assembly of the numerical arrays are distinguished in
Sections~\ref{sec:linear219}--\ref{sec:parity221}.''', r'''For the fixed 98-edge parent, the complete prefix cover and exact
leaf certificates exclude every 93-edge partner at both endpoints.
Thus arbitrary compatible partners have at most 92 edges, and a
one-crossing join using this full parent or any cube-isometric copy
has at most 191 edges. No compatible 92-edge witness or attainment is
claimed. Exact fractional assignments still satisfy every occupancy-cycle,
subset-forest and disagreement-cycle parity inequality at total weight
94 in the unconditioned model. The actual-path prefix division excludes
the Boolean completions. Four new generic results pass Lean; finite
coverage, concrete model validity and exact coefficient arithmetic have
separate independent audits, with end-to-end Lean assembly of those
numerical records still absent. These scopes are distinguished in
Sections~\ref{sec:linear219}--\ref{sec:prefix222}.''')

bib = r'''\bibitem{research222}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Complete prefix certificates
and a one-crossing ceiling for the saved parent class}.
Research milestone 222, 15 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/222-prefix-certificates}.

'''
main = once(main, r'\bibitem{barahona1986}', bib + r'\bibitem{barahona1986}')

short = before[names[1]].decode('utf-8')
short = once(short, r'\date{Research state after round 221}',
             r'\date{Research state after round 222}')
start = short.index(r'\section{A direct partner target and the fractional obstruction}')
end = short.index(r'\section{Remaining questions}', start)
direct = r'''\section{The completed fixed-parent exclusion}
Let $P$ be the saved 98-edge $Q_8$ parent and $t$ either endpoint, 0 or 78.
A 93-edge induced path beginning at $t$ and avoiding $V(P)\setminus\{t\}$
would give $98+93+1=192$ edges after one crossing. Each permitted graph
has 158 vertices and 337 edges. Earlier degree-and-cycle searches returned
\texttt{UNKNOWN}; the prefix certificates below now exclude both targets.

A 93-edge partner has 47 vertices of each parity and an odd free endpoint.
The model gives degree one to the two selected endpoints and degree two
to other selected vertices, with $y_{ab}=x_ax_b$ for Boolean selections.
An induced path omits a vertex of every cycle: its last cycle vertex
cannot have two distinct earlier cycle neighbours, since both would be
its immediate predecessor. Lean checks the parity and cycle implications.

For every allowed subset $U$ and $v\in U$, selected edges also satisfy
\[
\sum_{ab\in E(U)}y_{ab}\le\sum_{u\in U}x_u-x_v.
\]
Here $E(U)$ contains the allowed edges within $U$. Inducedness assigns
each selected edge to a distinct selected path index, avoiding a selected
marked index. This proves the inequality; the unselected case is weaker.
If $X,Y,B,E$ count selected vertices, internal edges, boundary edges and
selected endpoints in $U$, degree accounting gives $2X-E=2Y+B$.
Thus the same inequality is $B+E\ge2x_v$. These deductions pass Lean.

For Boolean products, $\delta_{ab}=x_a+x_b-2y_{ab}$ records endpoint
disagreement. A closed cycle changes value an even number of times.
An odd marked edge set $F$ must differ from that pattern somewhere, giving
\[
\sum_{e\in F}\delta_e-\sum_{e\in E(C)\setminus F}\delta_e\le|F|-1.
\]
Lean checks the arbitrary closed-walk argument. These inequalities are
classical~\cite{barahona1986}. The preceding finite comparison gave exact
cardinality bounds 95.955197 and 95.763979, excluding 95-edge partners.

\paragraph{Why the continuous model alone remains insufficient.}
The exact fractional feasible cardinalities are
\[
q_0=\frac{2507137819890885477}{26128236866583647},\qquad
q_{78}=\frac{388107824092577}{4052758842992}.
\]
Both exceed 94 and satisfy all three complete inequality families.
For occupancy cycles, put $w_u=1-x_u$. For each deleted edge $ab$,
a potential satisfies $p_a=0$, $|p_u-p_v|\le w_u+w_v$ on other edges,
and $p_b+w_a+w_b\ge2$. Summing around any cycle gives
$\sum_{u\in C}w_u\ge1$. For subset inequalities, 158 feasible flows
per root send at least $2x_v$ from $v$ to an added sink. Conservation
bounds the supply by every separating cut, whose capacity is $B+E$.

For parity cycles, make two copies of each vertex. Edges preserving
the copy label cost $\delta_{ab}$; switching edges cost $1-\delta_{ab}$.
For each vertex, a saved potential increases by at least one between
its copies and satisfies $p(b)-p(a)\le c_{ab}$ on every directed arc.
A cycle switching on an odd marked set ends at the opposite copy.
Telescoping gives cost at least one, the required parity inequality.
Independent exact arithmetic audits verify these rational potentials and flows.

Mix either point with a one-edge path, using weight $92/(q_t-2)$ on
the larger point. The mixture has weight 94 and preserves all three
linear families. Thus this continuous relaxation still admits the target;
these fractional points supply no path~\cite{research220,research221}.

\paragraph{Complete division by actual prefixes.}
For a hypothetical path $q_0,\ldots,q_{93}$, each proper prefix with
$k<93$ requires $x_{q_i}=1$ for $0\le i\le k$ and $e_{q_i}=0$ for
$0<i\le k$. Injectivity makes every nonroot prefix vertex different
from both full endpoints, including the current last prefix vertex.
Its next vertex is allowed, adjacent to the last vertex, unused, and
nonadjacent to every earlier prefix vertex. Enumerating all such vertices
covers every possible continuation. Lean derives these necessities.

Each branch adds its prefix equalities to the model. Exact cardinality
bounds below 94 exclude branches; every other branch is expanded completely.
The audited counts, with depth measured in prefix edges, are
\[
\begin{array}{c|rrrrrr|r}
\text{Depth}&1&2&3&4&5&6&\text{Total}\\\hline
\text{Nodes}&14&33&21&9&1&2&80\\
\text{Excluded}&3&23&17&8&0&2&53\\
\text{Expanded}&11&10&4&1&1&0&27
\end{array}
\]
There are no pending leaves. Root 0 has 31 excluded leaves and root 78
has 22; their largest exact bounds are 93.963070 and 93.984077.
The unique depth-four survivor was $(78,206,198,196,197)$, followed
necessarily by 213 and then by either 215 or 221. The final bounds are
93.979475 and 93.414818. The initial low-memory interruption preserved
45 completed new queries and 20 pending prefixes; continuation completed
the cover. The failed batch remains recorded separately.

Every actual 93-edge partner must follow this complete tree to a leaf
of depth at most six. Its 94 selected vertices contradict that leaf's
bound below 94; all used prefixes are proper because $6<93$.
Every longer partner has a compatible 93-edge prefix. Therefore
\[
\boxed{\text{partner length}\le92,\qquad
\text{one-crossing joining length}\le98+92+1=191.}
\]
An inverse cube isometry preserves length, inducedness, the joining
endpoint and parent avoidance, so the ceiling holds for the full
cube-isometry class of this parent. This pullback is also checked in Lean.
No compatible 92-edge witness or attainment of 191 by this construction
is established. Different parent classes and other face arrangements
are outside the exclusion.

Four generic results in two Lean modules support the prefix and isometry
arguments. Complete finite coverage and numerical certificates have
independent exact audits, with concrete model necessity reviewed separately.
The numerical tree and coefficient arrays have no end-to-end Lean assembly.
All evidence is retained in milestone 222~\cite{research222}.

'''
short = short[:start] + direct + short[end:]
short = once(short, r'''A compatible 93-edge partner would improve the lower bound to 192.
A different parent or face arrangement remains possible, but finding a
new $Q_8$ parent alone does not supply a compatible $Q_9$ construction.''', r'''A one-crossing join using the full saved parent class cannot improve 191.
Further construction work can use a different parent isometry class,
a shorter parent with a sufficiently long compatible partner, or multiple
crossings. Finding a new parent still requires a compatible joining construction.''')
short = once(short, 'milestones through round 221.', 'milestones through round 222.')
short = once(short, r'\bibitem{barahona1986}', bib + r'\bibitem{barahona1986}')

after = {names[0]: main.encode('utf-8'), names[1]: short.encode('utf-8')}
for name in names:
    old_text, new_text = before[name].decode('utf-8'), after[name].decode('utf-8')
    if old_text.split(r'\date{')[0] != new_text.split(r'\date{')[0]:
        raise RuntimeError('Preamble changed: ' + name)
    if not set(re.findall(r'\\label\{([^}]+)\}', old_text)) <= set(re.findall(r'\\label\{([^}]+)\}', new_text)):
        raise RuntimeError('Existing label removed: ' + name)
    for path in (EDITOR / name, R / 'paper' / name):
        if path.read_bytes() not in (before[name], after[name]):
            raise RuntimeError('Unexpected concurrent source change: ' + str(path))

for name in names:
    (EDITOR / name).write_bytes(after[name])
    (R / 'paper' / name).write_bytes(after[name])

record = {
    'status': 'SAVED_SOURCE_REVISION_NOT_COMPILED_BY_THIS_SCRIPT',
    'script_sha256': sha(Path(__file__).read_bytes()),
    'audit_pins': audit_pins,
    'files': {name: {'before_sha256': sha(before[name]), 'after_sha256': sha(after[name]),
                    'editor': str(EDITOR / name), 'mirror': str(R / 'paper' / name),
                    'lines': len(after[name].splitlines())} for name in names},
    'preserved': ['authors', 'hypersetup', 'all previous labels', 'historical results'],
    'compilation': 'Not run; parent owns compilation after the source revision.'
}
(H / 'data' / 'paper-revision.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
print(json.dumps(record, indent=2))
