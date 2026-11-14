"""Update only the contributor-233 status passages; preserve historical calculations."""
from pathlib import Path
import hashlib
import re

H = Path(__file__).resolve().parents[1]
EDITOR = Path('D:/Codex/2026-10-13/new-chat/outputs')
PAPER = Path('E:/Snake-in-a-box/paper')

def once(s, old, new):
    if s.count(old) != 1:
        raise RuntimeError(f'Expected one passage, found {s.count(old)}: {old[:100]}')
    return s.replace(old, new, 1)

def protected(s):
    return (re.findall(r'^\\author\{.*$', s, re.M),
            re.findall(r'\\hypersetup\{.*?^\}', s, re.M | re.S))

main_name = 'snake9_research.tex'
front_name = 'snake9_frontier_explanation.tex'
original = {name: (EDITOR / name).read_bytes() for name in [main_name, front_name]}
for name, raw in original.items():
    backup = H / 'data' / ('before-' + name)
    if not backup.exists():
        backup.write_bytes(raw)
    elif backup.read_bytes() != raw:
        raise RuntimeError('Existing backup differs; preserve it and review before rerunning.')
    if (PAPER / name).read_bytes() != raw:
        raise RuntimeError('Editor and repository mirror differ before editing: ' + name)

s = original[main_name].decode('utf-8').replace('\r\n', '\n')
s = once(s, r'\date{\today}', r'\date{Research state after round 213, 15 November 2026}')
s = once(s, '''a completed archived contributor theorem give $191\\le a(9)\\le235$.
The saved upper-bound audit is successful; its complete independent
rebuild remains pending.''', '''a completed contributor theorem give $191\\le a(9)\\le233$.
The pinned contributor source has no remaining certificate or floor
premise, and its saved final assembly and axiom audit are successful.
A complete independent rebuild remains pending~\\cite{bound233archive}.''')
s = once(s, '''would give $a(9)\\le234$. A separate contributor comparison targets 233.''', '''would give $a(9)\\le234$. This alternative comparison is numerically
superseded by the completed contributor bound 233; its own premises
remain unresolved.''')
s = once(s, '''enumerations and unresolved premises. No construction above 191 or
improved unconditional numerical bound is obtained. The value 196''', '''enumerations and unresolved premises. The contributor bound improves
the archived upper bound from 235 to 233; no construction above 191
is obtained. The value 196''')
s = once(s, r'\boxed{191\le a(9)\le235.}', r'\boxed{191\le a(9)\le233.}')
s = once(s, '''The upper bound is the completed contributor theorem at the cited archival
revision, with a successful saved compilation and axiom audit. A complete
independent rebuild of its dependency closure remains pending.''', '''The upper bound is the completed contributor theorem at revision
\\texttt{b0521e1d}, with its final assembly and axiom audit recorded at
\\texttt{b65d30ca}~\\cite{bound233archive}. Its theorem has no remaining
certificate or floor premise. A complete independent rebuild of its
dependency closure remains pending.''')
old = '''The lower bound is verified from the explicit transition sequence in Theorem~\\ref{thm:lower}. The archived upper-bound argument has three steps. First, count coordinate squares exactly and establish positive singleton counts, with a stronger contribution at each endpoint. Second, exclude a finite family of local configurations and verify an integer potential on every remaining transition. Third, sum the potential inequalities and substitute the resulting count estimate into the square identity. Section~\\ref{sec:upper-proof} records this argument for 235.'''
new = '''The lower bound is verified from the explicit transition sequence in
Theorem~\\ref{thm:lower}. The completed upper bound combines the square
census, local count and share certificates, and a finite potential summed
along every actual snake. Section~\\ref{sec:bound233} records the completed
233 chain. Section~\\ref{sec:upper-proof} preserves the earlier 235 argument
and its empty-square refinement with their original constants.'''
s = once(s, old, new)
s = once(s, '''remaining conditions for bounds 234 and 233.''', '''completed contributor bound 233 and the remaining conditions for
alternative 234 and relaxed 233 comparisons.''')
s = once(s, '''$a(9)\\le235$ & Archived contributor proof using 1287 local keys and a potential; the full independent rebuild remains pending.\\\\''', '''$a(9)\\le233$ & Completed contributor theorem with saved final assembly and standard-axiom audit; full independent rebuild pending.\\\\
Historical bound 235 & Archived proof using 1287 local keys and a potential; its count identities remain useful, while the numerical bound is superseded.\\\\''')
s = once(s, '''Conditional bound 233 & Contributor chain and saved Linux evidence inspected; production local certificates remain pending. New boundary accounting permits four units of share allowance, with the actual-snake integration unfinished.\\\\''', '''Relaxed 233 comparison & The original contributor chain is complete. The separate four-unit share allowance retains its own relaxed coverage and actual-snake integration premises.\\\\''')
s = once(s, '''Conditional bound 234 & Profile''', '''Alternative conditional 234 & Numerically superseded by 233. Profile''')
s = once(s, r'\section{The upper bound 235 and the retained empty-square term}\label{sec:upper-proof}', r'''\section{The upper bound 235 and the retained empty-square term}\label{sec:upper-proof}
This section preserves the earlier count-only argument and its original
constants. Its numerical upper bound is superseded by the completed
contributor theorem in Section~\ref{sec:bound233}; the identities and
conditional refinements below retain their stated mathematical scope.''')
completed = r'''\section{Completed contributor bound 233}\label{sec:bound233}
The contributor theorem at revision \texttt{b0521e1d} states that every
snake in $Q_9$ has at most 233 edges~\cite{bound233archive}. Its final source
applies the two completed local-certificate aggregates to the B233
comparison, with all five required share floors already supplied.
The separate relaxed comparison below is not required by this theorem.

For $m\ge7$, let $W$ denote the original B233 total window weight.
The completed window potential and original charge accounting give
\[
520(m-7)\le W+1023,\qquad W+4200m\le1099800.
\]
The first inequality telescopes over the $m-7$ windows; the second
combines their singleton and share contributions with the square census.
The finite table checks, exclusion certificates and share-floor proofs
supply these inequalities for every actual snake in the contributor chain.
Eliminating $W$ gives
\[
4720m\le1104463<1104480=4720\cdot234.
\]
The gap at length 234 is 17, so integrality gives $m\le233$.
Lengths $m<7$ satisfy the conclusion directly.

The saved Linux audit at \texttt{b65d30ca} records successful final
assembly and only \texttt{propext}, \texttt{Classical.choice} and
\texttt{Quot.sound} for both the upper theorem and the $191$--$233$
interval theorem. It reused 172 of 173 chain modules. Its dependencies
include an external floor-object overlay and nineteen cloud-built
certificates imported after hash and toolchain checks. Generated
certificate sources were deleted after compilation, and some earlier
replay objects were migrated with preserved modification times.
An independent full source rebuild and independent recheck of those
imported objects remain pending. These are verification limitations,
not additional hypotheses in the final upper-bound theorem.

'''
s = once(s, r'\subsection{Reducing the share requirements in the six-step comparison}\label{sec:slack233}', completed + r'\subsection{Reducing the share requirements in the six-step comparison}\label{sec:slack233}')
s = once(s, '''The contributor's six-step comparison now has a checked conditional
implication to $m\\le233$, with its production local certificates still
pending. Its saved source and compilation record have been inspected;
an independent rebuild is incomplete. The following deduction weakens
the share premises while preserving the original table and potential.''', '''The original contributor six-step comparison is complete, as recorded
in Section~\\ref{sec:bound233}. The following separate deduction weakens
its share requirements while preserving the original table and potential.
The relaxed coverage and actual-snake integration require their own proofs;
they are not premises of the completed original theorem.''')
s = once(s, '''requirements remain unchanged. Thus 233 remains conditional.''', '''requirements for this relaxed route remain unchanged. This alternative
route to 233 remains conditional; the original contributor route is complete.''')
s = once(s, r'\section{Remaining requirements for a stronger bound}\label{sec:closure}', r'''\section{Remaining requirements for alternative comparisons}\label{sec:closure}
The completed contributor bound 233 numerically supersedes the proposed
234 comparisons and matches the relaxed 233 target. The requirements
below concern those separate arguments; they do not qualify the completed
theorem of Section~\ref{sec:bound233}.''')
s = once(s, '''The maintained interval is $191\\le a(9)\\le235$, with the contributor-proof''', '''The maintained interval is $191\\le a(9)\\le233$, with the contributor-proof''')
s = once(s, '''The principal remaining work is to
establish the weakened local share floors and every retained graph
assumption.''', '''Completing this alternative argument requires establishing the weakened
local share floors and every retained graph assumption.''')
start = s.index(r'\section{Verification scope and remaining problem}\label{sec:verification}')
end = s.index('\nIn the newer share argument,', start)
s = s[:start] + r'''\section{Verification scope and remaining problem}\label{sec:verification}
The maintained interval is $191\le a(9)\le233$. The lower bound follows
from the explicit witness. The completed contributor upper theorem and
its saved final assembly and axiom audit are pinned to revisions
\texttt{b0521e1d} and \texttt{b65d30ca}~\cite{bound233archive}.
Section~\ref{sec:bound233} gives the original B233 charge and potential
deduction. No certificate or floor premise remains in that theorem.
The audit reused 172 chain modules and depended on external floor and
cloud-built objects; an independent full rebuild remains pending.
The earlier 235 theorem, its independent numerical potential reconstruction
and its retained empty-square argument are preserved as historical results
in Section~\ref{sec:upper-proof}~\cite{bound235archive}.
''' + s[end:]
s = once(s, '\nIn the newer share argument,', '\nIn the separate retained share argument,')
s = once(s, '''Section~\\ref{sec:floor14-loss}. The separate conditional-233 comparison
and its four-unit share allowance retain their stated local-certificate
and actual-snake integration requirements.''', '''Section~\\ref{sec:floor14-loss}. These conditional 234 comparisons are
numerically superseded by the completed contributor theorem. The separate
four-unit-allowance comparison in Section~\\ref{sec:slack233} retains its
own relaxed local-coverage and actual-snake integration requirements.''')
bib = r'''\bibitem{bound233archive}
Snake-in-the-box project contributors. \emph{Completed share-weighted bound
233: final assembly, standard-axiom audit and verification limitations}.
Contributor revision \texttt{b0521e1d14fd52c62db4cdeccc356b70a623eb82};
audit revision \texttt{b65d30ca15441420b8f4538f671e589c2502674f},
14 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/b0521e1d14fd52c62db4cdeccc356b70a623eb82/milestones/33-233-lean}.

'''
s = once(s, r'\bibitem{bound235archive}', bib + r'\bibitem{bound235archive}')
s = once(s, 'improve the project interval $191\\le a(9)\\le235$, whose upper bound retains the archived-proof qualification.', 'improve the then-maintained interval $191\\le a(9)\\le235$, whose upper bound retained the archived-proof qualification. The current contributor bound is recorded in Section~\\ref{sec:bound233}.')
s = once(s, 'supplies the project interval $191\\le a(9)\\le235$, with the complete independent rebuild still pending.', 'supplied the then-maintained interval $191\\le a(9)\\le235$, with the complete independent rebuild still pending. Section~\\ref{sec:bound233} records the subsequently completed contributor bound 233.')

f = original[front_name].decode('utf-8').replace('\r\n', '\n')
f = once(f, 'Research state after round 212', 'Research state after round 213')
f = once(f, '''The verified $Q_9$ construction has 191 edges. The archived contributor
theorem $a(9)\\le235$ has a successful saved compilation and axiom audit;
its complete independent rebuild remains pending. The proposed
improvements to 234 and 233
retain explicit unproved premises. Thus the archived project interval
is $191\\le a(9)\\le235$, with different verification histories at its ends.''', '''The verified $Q_9$ construction has 191 edges. The contributor's completed
theorem gives $a(9)\\le233$, with no remaining certificate or floor premise
and a successful saved final assembly and axiom audit. Thus the maintained
interval is $191\\le a(9)\\le233$. An independent full rebuild remains
pending. The source is pinned to \\texttt{b0521e1d}, with the audit at
\\texttt{b65d30ca}~\\cite{bound233archive}. The alternative conditional 234
and relaxed 233 arguments below retain their own unproved premises.''')
f = once(f, '''It yields 235, and a hypothetical 235-edge snake must have $s_0\\le13$.''', '''This historical argument yields 235, numerically superseded by the
completed bound 233. Under its own premises, a hypothetical 235-edge
snake must have $s_0\\le13$.''')
f = once(f, r'\section{How empty squares could improve the bound}', r'\section{Empty-square shares and upper bounds}')
f = once(f, 'That additional assertion is open. The strengthened boundary deduction', 'That assertion was an unresolved premise of this historical route; the\ncompleted 233 theorem excludes length 235 independently. The strengthened boundary deduction')
f = once(f, '''For $m\\ge9$ in the retained nine-transition comparison, let $W$ be the total''', r'''\subsection{The completed contributor comparison}
For $m\ge7$, let $W$ be the original B233 total window weight. The completed
local certificates, share floors and finite potential give
\[
520(m-7)\le W+1023,\qquad W+4200m\le1099800.
\]
Therefore
\[
4720m\le1104463<4720\cdot234=1104480,
\]
so $m\le233$; shorter snakes satisfy the bound directly.
The final audit reports only Lean's standard axioms. It reused 172 of 173
chain modules, with external floor objects and nineteen cloud-built
certificates. A fresh independent rebuild and recheck of imported objects
remain pending~\cite{bound233archive}.

\subsection{A separate retained comparison}
For $m\ge9$ in the retained nine-transition comparison, let $W$ be the total''')
f = once(f, '''conditional. The older accepted-key graph''', '''conditional and is numerically superseded by the completed 233 theorem.
The older accepted-key graph''')
f = once(f, '''A separate contributor comparison uses $m-7$ windows and''', '''A separate relaxation of the completed contributor comparison uses
$m-7$ windows and''')
f = once(f, '''would give 233. The relaxed share coverage, required local certificates
and actual-snake integration remain separate obligations. Compilation
progress on individual modules does not by itself discharge them.''', '''would also give 233. The relaxed share coverage and its actual-snake
integration remain separate obligations. These unresolved requirements
belong to this modified argument; the original contributor theorem is complete.''')
f = once(f, '''The upper-bound route needs its remaining local certificates,
geometric interpretations and complete graph-to-snake argument.''', '''The current upper bound is 233. A smaller bound requires a stronger
argument. The alternative comparisons above retain their own local
certificates, geometric interpretations and complete graph-to-snake
requirements, despite being numerically superseded.''')
f = once(f, 'retained in the companion manuscript and milestones through round 212.', 'retained in the companion manuscript and milestones through round 213.')
f = once(f, r'\end{document}', '\\begin{thebibliography}{1}\n' + bib + '\\end{thebibliography}\n\\end{document}')

updated = {main_name: s, front_name: f}
for name, text in updated.items():
    old_text = original[name].decode('utf-8').replace('\r\n', '\n')
    if protected(old_text) != protected(text):
        raise RuntimeError('Protected author or hypersetup content changed: ' + name)
    newline = '\r\n' if b'\r\n' in original[name] else '\n'
    raw = text.replace('\n', newline).encode('utf-8')
    (EDITOR / name).write_bytes(raw)
    (PAPER / name).write_bytes(raw)
    print(name, len(raw), hashlib.sha256(raw).hexdigest())

report = '''# Contributor-status manuscript update

Round 213, 15 November 2026. Updated the two existing editor manuscripts in place and wrote identical bytes to their repository mirrors. Before-edit bytes are preserved once in `data/before-snake9_research.tex` and `data/before-snake9_frontier_explanation.tex`.

Main manuscript changes: date; abstract; principal interval and proof-dependency paragraph; current-status table; historical qualifier at the 235 argument; new `sec:bound233` with the original completed B233 chain and exact margin 17; scope of `sec:slack233`; alternative-comparison closure; verification-status paragraphs; new `bound233archive` bibliography entry pinned to b0521e1d/b65d30ca.

Frontier changes: round/date; opening interval and evidence statement; historical qualification of 235; completed B233 deduction within the share section; explicit distinction between the completed original chain and alternative retained/relaxed comparisons; remaining-problem paragraph; round cutoff and pinned bibliography entry.

Preserved: both complete author declarations and every existing hypersetup block exactly; historical 235 formulas and calculations; the relaxed four-unit inequality, conditional retained 234 formulas and their unresolved premises; construction and native-search records. The completed theorem has no certificate/floor premise. The saved incremental audit reused 172 modules, external floor objects and nineteen cloud-built certificates; independent full rebuilding remains pending. No new mathematical claim beyond the inspected contributor source was added.

No compiler was run by this editor. The parent owns compilation and subsequent geometry additions. This report records source changes only; it does not claim successful document compilation.
'''
(H / 'logs/document-status-review.md').write_text(report, encoding='utf-8', newline='\n')
