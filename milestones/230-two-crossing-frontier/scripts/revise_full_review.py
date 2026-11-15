"""Apply the round-230 full-source editorial review to the frozen round-229 text.

Run without arguments to print the proposed hashes. Use --apply only after the
parent has finished the active workers, before adding round-230 mathematical text.
This script runs no compiler, solver or tests. It changes no mathematical result.
"""

import argparse
from collections import Counter
from hashlib import sha256
from pathlib import Path
import re


ROOT = Path("E:/Snake-in-a-box")
ORIGINALS = Path("D:/Codex/2026-10-13/new-chat/outputs")
ROUND = ROOT / "milestones/230-two-crossing-frontier"
EXPECTED = {
    "snake9_research.tex": "b573c89528302c48b8e1964517fb85ed9330a7b6ef50787e7af91f5ea214e00a",
    "snake9_frontier_explanation.tex": "f8e2767d7ea5d93e0e6c0799e65194b0d36f3634d513d0e96b61b0fb1e8a71f4",
}


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise ValueError(f"Expected exactly one editorial anchor: {old[:100]!r}")
    return text.replace(old, new, 1)


def revise_main(text):
    abstract_start = text.index(r"\begin{abstract}")
    abstract_end = text.index(r"\end{abstract}") + len(r"\end{abstract}")
    text = replace_once(text, text[abstract_start:abstract_end], r"""\begin{abstract}
Let $a(9)$ be the maximum edge length of an induced path in the
nine-dimensional binary hypercube. An explicit checked construction and
a completed contributor theorem give $191\le a(9)\le233$. The upper
theorem has a successful saved final assembly and axiom audit, with no
remaining certificate or share-floor premise; a complete independent
rebuild remains pending~\cite{bound233archive}.

The upper-bound analysis combines an exact coordinate-square census,
local count and empty-square share inequalities, and finite potentials.
Earlier bounds and alternative conditional comparisons retain their
original hypotheses and verification limits.

The construction analysis gives criteria for joining lower-dimensional
paths, changing coordinate histories, and replacing separated portions
of a known snake. A complete prefix cover with exact weighted-inequality
certificates excludes every 93-edge compatible partner of the saved
98-edge parent. Its full cube-isometry class therefore has a
one-crossing joining ceiling of 191 edges, without an attainment claim.
The unconditioned continuous model nevertheless admits exact fractional
weight 94 under all cycle occupancy, subset forest and cycle parity
inequalities. Native searches also exclude specified two-block
construction families, with the crossing restrictions and unresolved
cases stated explicitly.

Written proofs, Lean-checked implications and independently audited
numerical evidence are distinguished throughout. No construction above
191 or matching global upper bound is obtained. The numerical conjecture
$a(9)=196$ remains separate from every proved result.
\end{abstract}""")

    text = replace_once(text, r"""The argument has two parts. The first develops the square census,
local count restrictions and empty-square shares, then states the precise
completed contributor bound 233 and the remaining conditions for
alternative 234 and relaxed 233 comparisons. The seven-count boundary
allows the current retained comparison to use nonnegative loss alone.
The second examines numerical conjectures, constructions across
dimensions, transformations of whole snakes and restrictions obtained
by fixing coordinate histories. The final section records verification
scope and the unresolved extremal problem. Historical comparison models,
restricted construction experiments and explicit witnesses are retained
in the appendices. Every historical comparison keeps its original graph,
weights and boundary; later improvements do not silently change its premises.""", r"""\paragraph{Reading order and status.}
The strongest conclusions can be read before the chronological development:
\begin{itemize}
\item Section~\ref{sec:bound233} gives the completed contributor bound 233.
The square census and local inequalities preceding it explain its methods;
the alternative conditional 234 and relaxed 233 comparisons retain their
own unresolved premises.
\item Section~\ref{sec:prefix222} gives the exact fixed-parent ceiling of
191 for a one-crossing join. It covers the specified full parent and its
cube-isometry class, and asserts no compatible witness attaining that ceiling.
\item Sections~\ref{sec:replacement225}--\ref{sec:projection229} give the
simultaneous-replacement criteria and the successive restricted construction
results. Their native exclusions concern the stated seed, endpoint,
intervals and crossing conditions.
\item Section~\ref{sec:verification} separates completed implications,
numerical evidence and remaining verification obligations. The conjecture
in Section~\ref{sec:hypothesis} is used in none of these results.
\end{itemize}
The two parts retain the upper-bound and construction developments in
their mathematical order. Intermediate search outcomes are historical
records at their named cutoffs; a later exclusion supersedes an earlier
timeout only within the same covered family. The appendices retain earlier
comparison models, experiments and explicit witnesses. Every comparison
keeps its original graph, weights and boundary.

The following table records the upper-bound development and selected
local results. The construction conclusions are located by the guide above.""")

    edits = [
        ("Three consequences guide the next computation. First, keeping the effective",
         "Three consequences describe this historical comparison. First, keeping the effective"),
        ("A useful next local target is to exploit this restricted rounding loss.",
         "This restricted rounding loss gives a separate local proof target."),
        ("The omitted-count contribution improves from fourteen in the contributor's\npresent accounting to twenty-two, a gain of $120\\cdot8=960$.",
         "The omitted-count contribution improves from fourteen in the original\ncontributor accounting to twenty-two, a gain of $120\\cdot8=960$."),
        (r"""\label{sec:middle-replacements}
The common construction family""", r"""\label{sec:middle-replacements}
This subsection records the round-189 replacement restrictions. The later
eight-omission requirement in Section~\ref{sec:attachment-colour} strengthens
their numerical conclusion for the same fixed middle path.
The common construction family"""),
        ("The unrestricted five-omission circuit search remains unresolved after\n120 seconds, and a separate two-interval circuit search remains unresolved\nafter 60 seconds. A direct enumeration resolves the latter case.",
         "The initial unrestricted five-omission circuit query returned unknown\nafter 120 seconds, as did the separate two-interval query after 60 seconds.\nThe direct enumeration below then resolved the latter case."),
        (r"""This condition can restrict the larger-block search before enumeration;
it does not ensure that a replacement exists. The next construction
search can impose all these blocker requirements and target a
192-edge path directly. Evidence and remaining scopes are recorded
in~\cite{block193archive}.""", r"""This condition restricts the larger-block search before enumeration;
it does not ensure that a replacement exists. The subsequent search in
Section~\ref{sec:target194} imposes these blocker requirements and targets
a 192-edge path directly. Evidence and remaining scopes are recorded
in~\cite{block193archive}."""),
        (r"""in~\cite{symmetry198archive}. The next unrestricted construction search
can use the three endpoint cases. The simpler family avoiding all matching""",
         r"""in~\cite{symmetry198archive}. The three endpoint cases were subsequently
queried in Section~\ref{sec:symmetry199}. The simpler family avoiding all matching"""),
        (r"""\label{sec:direct217}
Longer submitted jobs""", r"""\label{sec:direct217}
This subsection records the round-217 search state. The fixed-parent
target introduced here was later excluded in Section~\ref{sec:prefix222};
the separate coordinate-history search remains unresolved.
Longer submitted jobs"""),
        ("Thus finding a different optimal parent is an additional discovery\nstage that is unnecessary for the still-open 192-edge target.",
         "At that cutoff, finding a different optimal parent was an additional\ndiscovery stage, unnecessary for the then-open fixed-parent target."),
        (r"""queries. They leave both endpoints unresolved, and no runtime advantage
over the earlier circuit formulation is established.""", r"""queries. Those queries also returned unknown at both endpoints; the later
prefix exclusion supersedes these timeouts. No runtime advantage over the
earlier circuit formulation is established."""),
        ("The unresolved cases remain open. No longer snake or global numerical bound is obtained, and no speed comparison is established.",
         "Both cases were unresolved at the round-218 cutoff; Section~\\ref{sec:prefix222} later excludes them. These queries gave no longer snake or global numerical bound, and established no speed comparison."),
        ("For 44-edge blocks, the 301 maximal contexts\ngive 107 geometric exclusions, 102 solver exclusions and 92 unresolved\ncases.",
         "At the round-224 cutoff, the 301 maximal width-44 contexts\ngave 107 geometric exclusions, 102 solver exclusions and 92 unresolved\ncases."),
        ("All 16 remain unknown, leaving 92 unresolved contexts. No new snake or\nglobal bound is obtained",
         "All 16 queries returned unknown, leaving 92 unresolved contexts at that\ncutoff. Section~\\ref{sec:lowerpair227} later completes this family. No new\nsnake or global bound was obtained"),
        ("Direct enumeration of connected\nreplacement paths is the next construction step.",
         "Direct enumeration of connected\nreplacement paths was the subsequent construction step."),
        ("Both searches remain incomplete\nand retain their frontiers.",
         "Both searches stopped incomplete and retained their frontiers;\nSection~\\ref{sec:residual226} later excludes their width-43 family."),
        ("The native direct searches remain incomplete. A block-chain refinement",
         "The direct searches stopped incomplete; the later reduced queries in\nSection~\\ref{sec:lowerpair227} supersede the relevant width-44 frontier.\nA block-chain refinement"),
        (r"""Future construction searches must change the scope, for example by
allowing wider blocks, another endpoint or another seed~\cite{research227}.""",
         r"""This exclusion required subsequent searches to change the scope.
Sections~\ref{sec:width45} and~\ref{sec:projection229} treat wider blocks
and variable crossing counts; other endpoints and seeds remain possible
choices~\cite{research227}."""),
        ("Wider blocks and different seeds or endpoints remain construction\npossibilities~\\cite{research228}.",
         "The width-46 continuation appears in Section~\\ref{sec:projection229};\ndifferent seeds or endpoints remain construction possibilities~\\cite{research228}."),
        (r"""The round-220 full-source review corrects historical proof references,
notation and current-status statements; it does not rebuild the entire
archived contributor chain.""", r"""Full-source reviews at rounds 220 and 230 check the written argument,
historical status, dependencies and presentation. They do not rebuild the
archived contributor chain or replay every numerical certificate."""),
        ("For the fixed eight-dimensional seed, searches for partner lengths 93, 92, and 91 at both endpoints were each unresolved after 30 seconds.",
         "For the fixed eight-dimensional seed, the early searches for partner lengths 93, 92, and 91 at both endpoints each returned unknown after 30 seconds. Section~\\ref{sec:prefix222} later excludes length 93; no compatible length-92 witness is established."),
        ("These restricted computational exclusions have not been independently certified; other length-98 seeds and multiple-crossing constructions remain possible.",
         "These initial solver exclusions had no independent contradiction certificates. Sections~\\ref{sec:forest220}--\\ref{sec:prefix222} later supply exact weighted-inequality certificates and a stronger ceiling for this parent class; other parent classes and multiple-crossing constructions remain possible."),
    ]
    for old, new in edits:
        text = replace_once(text, old, new)

    # Relocate the entire conjecture discussion without changing its contents.
    start = text.index(r"\section{A numerical conjecture and its limitations}")
    end = text.index(r"\section{Construction and the requirements for optimality}")
    conjecture = text[start:end]
    text = replace_once(text, conjecture, "")
    marker = r"\section{Verification scope and remaining problem}\label{sec:verification}"
    text = replace_once(text, marker, conjecture + marker)
    return text


def revise_short(text):
    edits = [
        ("The following counting and construction arguments address different parts\nof this task. Restricted search exclusions do not establish the global optimum.",
         "The counting argument supplies the upper bound. The construction arguments\nseek any improvement above 191, beginning with a 192-edge snake. Their\nrestricted exclusions do not establish the global optimum."),
        ("A closed cycle changes value an even number of times.",
         "A closed cycle $C$ changes value an even number of times."),
        (r"\section{Joint construction across four crossings}",
         r"\section{Joint construction across coordinate faces}"),
        ("The selected constructive route places three paths in one $Q_8$ face\nand two in the other.",
         "The initial four-crossing route places three paths in one $Q_8$ face\nand two in the other; the later replacement search also permits other\ncrossing counts."),
    ]
    for old, new in edits:
        text = replace_once(text, old, new)
    return text


def preserve_mathematical_content(before, after):
    # Editorial guards preserve named identities, complete statements and proofs,
    # all citation occurrences, and the original author/metadata preamble.
    patterns = [
        r"\\label\{[^}]+\}",
        r"\\cite(?:\[[^]]*\])?\{[^}]+\}",
        r"\\begin\{(theorem|proposition|lemma|corollary|conjecture|definition|remark|proof)\}.*?\\end\{\1\}",
    ]
    for pattern in patterns:
        old = Counter(m.group(0) for m in re.finditer(pattern, before, re.S))
        new = Counter(m.group(0) for m in re.finditer(pattern, after, re.S))
        if old != new:
            raise ValueError(f"Preservation guard failed: {pattern}")
    if before.split(r"\begin{document}", 1)[0] != after.split(r"\begin{document}", 1)[0]:
        raise ValueError("Preamble, authors or metadata changed")
    if before.split(r"\begin{thebibliography}", 1)[1] != after.split(r"\begin{thebibliography}", 1)[1]:
        raise ValueError("Bibliography changed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()
    pending = []
    for name, digest in EXPECTED.items():
        original = ORIGINALS / name
        mirror = ROOT / "paper" / name
        snapshot = ROUND / "data" / (name + ".before.txt")
        for path in (snapshot, original, mirror):
            if sha256(path.read_bytes()).hexdigest() != digest:
                raise ValueError(f"Frozen source changed: {path}")
        before = original.read_bytes().decode("utf-8")
        after = revise_main(before) if name == "snake9_research.tex" else revise_short(before)
        preserve_mathematical_content(before, after)
        data = after.encode("utf-8")
        pending.append((original, mirror, data))
    # Prepare and validate both texts before any source mutation.
    for original, mirror, data in pending:
        if args.apply:
            original.write_bytes(data)
            mirror.write_bytes(data)
        print(f"{'APPLIED' if args.apply else 'PROPOSED'} {original.name} {sha256(data).hexdigest()}")


if __name__ == "__main__":
    main()
