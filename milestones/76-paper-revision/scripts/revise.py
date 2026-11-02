"""Revise the existing paper in place, preserving exact preamble and prior statements."""
from pathlib import Path
import hashlib, json, re

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
PAPER = ROOT / 'paper/snake9_research.tex'
EDITOR = Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
EXPECTED = 'd422a0b3dea2c2e81cb2d63294c14ff37b2237447faf5fca193ee2664951d341'
raw = PAPER.read_bytes()
assert raw == EDITOR.read_bytes()
(HERE / 'data').mkdir(exist_ok=True)
if hashlib.sha256(raw).hexdigest() != EXPECTED:
    record = json.loads((HERE / 'data/revision.json').read_text(encoding='utf-8'))
    assert hashlib.sha256(raw).hexdigest() == record['paper_sha256'], 'Unrecorded manuscript edit'
    raw = (HERE / 'data/paper-before.tex.snapshot').read_bytes()
assert hashlib.sha256(raw).hexdigest() == EXPECTED
(HERE / 'data/paper-before.tex.snapshot').write_bytes(raw)
old = raw.decode('utf-8').replace('\r\n', '\n')
s = old

def replace(a, b):
    global s
    assert s.count(a) == 1, (s.count(a), a[:100])
    s = s.replace(a, b)

a = s.index(r'\begin{abstract}') + len(r'\begin{abstract}')
b = s.index(r'\end{abstract}', a)
abstract = r'''Let $a(9)$ be the maximum edge length of an induced path in the nine-dimensional binary hypercube. An explicit construction and a completed contributor proof give $191\le a(9)\le235$. We present the square census and local-count argument yielding $39m+2s_0\le9200$, where $s_0$ counts empty coordinate squares. Integer shares retain this empty-square term in local estimates. We develop share inequalities from forced absence, complete neighbour alternatives and singleton-count conditions, then prove count-independent share bounds for four six-transition shapes. A strengthened boundary estimate shows that nine-transition windows omit at least 21 singleton counts. Together with five-centre overlap accounting, it gives an explicit potential criterion for the upper bound 234. A complete finite comparison graph meets that criterion with mean 496 and potential range 600, but six local share premises, its complete arbitrary-snake interpretation and its Lean potential replay remain unfinished. A cycle and short-walk argument shows why six specified weakenings of that catalogue cannot be repaired solely by changing the potential. Exact history recognition and count-shift identities provide checked components of the remaining interpretation. Earlier models, sharpness witnesses and unsuccessful construction approaches are retained with their scopes. The proposed value 196 remains a conjecture without a matching construction or optimality proof.'''
s = s[:a] + '\n' + abstract + '\n' + s[b:]
a = s.index('The subsequent argument develops the empty-square term')
b = s.index(r'\begin{center}', a)
s = s[:a] + r'''The argument proceeds from local geometry to global accounting. Sections~\ref{sec:empty-packing}--\ref{sec:countfree-catalogue} develop integer shares, forced-absence estimates and local count restrictions. Section~\ref{sec:common-budget} states the overlap capacities. Section~\ref{sec:long-models} derives the strengthened boundary estimate and a precise sufficient condition for 234. Section~\ref{sec:current-model} defines the current finite model, compares completed and pending local evidence, proves the history invariant, and explains a short-walk obstruction to weakening the catalogue. Section~\ref{sec:closure} lists the remaining mathematical implications. The conjecture 196 and construction criteria follow. Historical finite models and all explicit witness sequences are retained in the appendices.

''' + s[b:]
replace(r'Finite-model mean $18823/4560$ & A cycle and an all-edge potential; inherited premises and complete snake coverage remain unfinished.\\',
        r'Conditional bound 234 & Mean 496, range 600 and boundary loss 21; six local shares and the complete graph proof remain pending.\\' + '\n' +
        r'History and obstruction results & Checked suffix recognition and short-walk algebra; finite graph witnesses are independently computed.\\')
# Retain superseded models and every old mathematical statement, with explicit time scope.
a = s.index(r'\subsection{The limit of reweighting a fixed local calculation}')
b = s.index(r'\section{Remaining requirements for a stronger bound}', a)
history = s[a:b]
history = history.replace('For the final complete model, this extraction gives',
                          'For the final model of that earlier comparison, this extraction gives')
history = history.replace('A stronger empty-square estimate must therefore control the whole remaining family and all possible replacements.',
                          'At that stage, strengthening the model required control of this entire family and possible replacements. The subsequent integration and revised proof-supported model are described in Section~\\ref{sec:current-model}.')
s = s[:a] + (HERE / 'text/current-model.tex').read_text(encoding='utf-8') + '\n' + s[b:]
replace(r'\appendix', r'\appendix' + '\n' +
        r'\section{Earlier complete finite models and their obstructions}\label{app:earlier-long-models}' + '\n' +
        'This appendix retains the earlier graph calculations and their original boundary estimates. Their exact finite statements remain valid for the recorded models. The current proof-supported comparison, stronger boundary estimate and remaining obligations are in Sections~\\ref{sec:boundary21}--\\ref{sec:closure}.\n\n' + history)
replace(r'\section{Combining local contributions without repeated counting}\label{sec:common-budget}',
        (HERE / 'text/local-catalogue.tex').read_text(encoding='utf-8') + '\n\n' +
        r'\section{Combining local contributions without repeated counting}\label{sec:common-budget}')
a = s.index(r'\section{Remaining requirements for a stronger bound}\label{sec:closure}')
b = s.index(r'\subsection{Sufficient charge inequalities}', a)
s = s[:a] + r'''\section{Remaining requirements for a stronger bound}\label{sec:closure}
The unconditional interval remains $191\le a(9)\le235$. Corollary~\ref{cor:eighteen-empty} shows that eighteen empty squares would suffice to exclude a hypothetical 235-edge snake. The current charge model already meets an equivalent sufficient numerical criterion, conditional on its remaining local and global proof obligations.

The required implication has the following ordered parts.
\begin{enumerate}
\item Complete the six pending count-independent share targets in Section~\ref{sec:countfree-catalogue}, including their geometric interpretation and reversal. The three stronger completed cases and the older distinct-direction share of twelve remain available independently.
\item Construct the exact graph walk from an arbitrary snake. Identify every nine-direction block in the 505-entry extension table, relate source and target to the 132 direction shapes, and connect the numeric history index to Lemma~\ref{lem:longest-suffix}.
\item Justify every exclusion guard and every credit lookup. For a three-label history, cover all compatible eleven-direction words. Apply the resulting share bounds to the same five centres and take their maximum. Checked shift and saturation lemmas supply components of this step.
\item Check the complete finite potential and its range in Lean, then telescope it along that walk and apply Proposition~\ref{prop:boundary21}. An independent integer check of all 4947008 edges is already recorded, but does not complete this Lean dependency chain.
\end{enumerate}
None of these requirements is supplied by an attaining cycle alone. The short-walk obstruction shows that merely omitting one of the six pending floors in the tested ways cannot be repaired by a different constant potential slope on the same relaxed graph. Reachability restrictions, further geometry or sharper boundary information could change that conclusion.

The contributor's separate seven-centre count-only proposal also targets 234. Its latest inspected production record retains unfinished local certificates and transition checks~\cite{conditional234archive}. It is distinct from the present five-centre share model and is not used to strengthen the main theorem.

''' + s[b:]
# Refresh verification scope as a complete section.
a = s.index(r'\section{Verification scope and remaining problem}\label{sec:verification}')
b = s.index(r'\appendix', a)
s = s[:a] + r'''\section{Verification scope and remaining problem}\label{sec:verification}
The global conclusion is $191\le a(9)\le235$. The lower bound follows from the explicit witness. The upper bound uses the square identity, endpoint estimates, all 1287 catalogue keys, a potential verified on every permitted transition, and the path summation. Its initial-count and potential losses are included. No conjecture or restricted construction search enters that argument.

The completed contributor theorem has a successful archived dependency audit~\cite{bound235archive}. Its assumptions have been discharged in that development; the audit lists propositional extensionality, classical choice and quotient soundness. The final theorem source and saved audit were reviewed, and the potential was independently reconstructed. A fresh independent rebuild of the entire 235 dependency closure remains pending. The earlier 236 and 238 proofs are retained with their own recorded audits.

Each completed local theorem has the scope stated in its proof. The relevant checks include clause semantics, contradiction replay, coordinate normalization and, where claimed, reversal. Complete paths establish the displayed sharpness claims. Local forests establish feasible local assignments only. The share identity, five-centre overlap, twenty-one-count boundary estimate, exact history invariant, count-code identities and conditional lookup have separate Lean checks. The new interface checks do not yet construct the complete graph walk.

Finite model minima are certified by an attaining cycle and a potential checked on every saved edge. The current comparison uses locally proved rules, and its stronger mixed catalogue retains six explicit share premises. Full graph interpretation and Lean potential replay remain unfinished in both comparisons. The six short-walk witnesses were checked by direct array computations; the algebraic obstruction was checked in Lean. These distinct evidence levels are retained in the cited archives.

No snake longer than 191 has been obtained in this work, and no matching upper bound has been established. The conditional 234 calculation is a specific proof target with a numerical margin of 32 at length 235. The remaining obligations in Section~\ref{sec:closure}, rather than a new extrapolation of the low-dimensional sequence, determine whether that target becomes a theorem. The value 196 remains unresolved.

''' + s[b:]
replace('and the direct proof of 236 is in Section~\\ref{sec:upper-proof}.',
        'and the direct proof of 236 is in Appendix~\\ref{app:bound236}.')
replace('improve the current interval $191\\le a(9)\\le236$.',
        'improve the current interval $191\\le a(9)\\le235$.')
replace('establishes the current interval $191\\le a(9)\\le236$.',
        'establishes the current interval $191\\le a(9)\\le235$.')
replace('This conditional estimate is weaker than the unconditional bound 236 in Theorem~\\ref{thm:upper236}.',
        'This conditional estimate is weaker than the upper bound 235 in Theorem~\\ref{thm:upper235}.')
replace('The first subsection records the current exact finite-model result used in Section~\\ref{sec:common-budget};',
        'The first subsection records the earlier seven-centre finite-model result discussed in Section~\\ref{sec:common-budget};')
replace('The radius-four refinement in Section~\\ref{sec:upper-proof} establishes the current interval',
        'The later six-centre proof in Section~\\ref{sec:upper-proof} establishes the current interval')
# Pin all newly cited results to inspected repository commits.
replace(r'\bibitem{conditional234archive}' + s.split(r'\bibitem{conditional234archive}')[1].split(r'\end{thebibliography}')[0],
        r'''\bibitem{boundaryarchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Critical-family charge and twenty-one-count boundary accounting}. Research milestone 67, included in pinned revision \texttt{990889da}.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/990889dac5a8502debd2187fe31b2f1edc08154b/milestones/67-critical-family-charge}.

\bibitem{currentarchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Proof-supported local models and interval-count proof closure}. Research milestones 70--72, included in pinned revision \texttt{990889da}.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/990889dac5a8502debd2187fe31b2f1edc08154b/milestones}.

\bibitem{countfreearchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Count-independent share catalogue, completed local certificates, and global accounting}. Research milestones 72--73, pinned revision \texttt{990889da}.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/990889dac5a8502debd2187fe31b2f1edc08154b/milestones/73-countfree-share-catalogue}.

\bibitem{obstructionarchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Graph interpretation audit and short-walk potential obstruction}. Research milestone 74, pinned revision \texttt{990889da}.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/990889dac5a8502debd2187fe31b2f1edc08154b/milestones/74-graph-interpretation-audit}.

\bibitem{historyarchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Exact history recognition, share selection and count-state identities}. Research milestone 75, pinned revision \texttt{990889da}.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/990889dac5a8502debd2187fe31b2f1edc08154b/milestones/75-exact-history-bridge}.

\bibitem{conditional234archive}
Snake-in-the-box project contributors. \emph{Seven-centre refinement toward 234: production proof and continuation record}. Latest inspected revision \texttt{1e0ebb95}, 2 November 2026. The production proof obligations remain incomplete.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/1e0ebb95954cc70f9edf59268b5a36df3f616422}.

''')
# Preserve the exact newline convention and both existing destinations.
out = s.replace('\n', '\r\n').encode('utf-8') if b'\r\n' in raw else s.encode('utf-8')
PAPER.write_bytes(out)
EDITOR.write_bytes(out)
record = dict(status='REVISED_PENDING_VERIFICATION', baseline_sha256=EXPECTED,
              paper_sha256=hashlib.sha256(out).hexdigest(), baseline_commit='990889dac5a8502debd2187fe31b2f1edc08154b',
              changes=['Updated abstract, roadmap, evidence table, verification and closure',
                       'Moved superseded complete-model discussion to a historical appendix',
                       'Added completed count-independent shares and conditional nine-shape catalogue',
                       'Added boundary21 proof and explicit234 potential criterion',
                       'Added current graph meaning, history proof and short-walk obstruction',
                       'Corrected two stale current236 statements and one historical cross-reference'],
              authors_and_hyperlink_settings='preserved', prior_theorem_statements='preserved',
              full_goal='Exact a(9) remains unresolved; no new global bound claimed')
(HERE/'data/revision.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps(record,indent=2))
