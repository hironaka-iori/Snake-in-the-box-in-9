"""Prepare revision 146 from the frozen revision-145 paper.

This file is intentionally prepared for inspection before execution. Running it
validates both authoritative copies and all preservation invariants before any
paper write, then saves the original, edits the open mirror, and synchronizes the
repository copy. It uses only the Python standard library and runs no external
program, proof assistant, solver, compiler or network request.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import tempfile


ROOT = Path("E:/Snake-in-a-box")
ROUND = ROOT / "milestones/146-initial-tree-and-paper"
REPO_PAPER = ROOT / "paper/snake9_research.tex"
OPEN_PAPER = Path("D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex")
BACKUP = ROUND / "audit/paper-before.tex.txt"
RECEIPT = ROUND / "data/paper-revision.json"
BRIDGE = ROUND / "data/bridge-completion.json"
EXPECTED_SHA256 = "c265a8cfd81812ae372e8568a7d45e898ba3e5d08affcbec911b0581d901f696"
EXPECTED_BRIDGE_STATUS = "PASS_ORIGINAL_CNF_TO_INITIAL_TREE_AND_CHECKED_PREFIX"

FORMAL = re.compile(
    r"\\begin\{(theorem|proposition|lemma|corollary|conjecture|definition)\}"
    r".*?\\end\{\1\}", re.S
)
PROOF = re.compile(r"\\begin\{proof\}.*?\\end\{proof\}", re.S)
BRACKET_MATH = re.compile(r"\\\[.*?\\\]", re.S)
ENV_MATH = re.compile(
    r"\\begin\{(equation\*?|align\*?|alignat\*?|gather\*?|multline\*?|displaymath)\}"
    r".*?\\end\{\1\}", re.S
)
QUOTE = re.compile(r"\\begin\{quote\}.*?\\end\{quote\}", re.S)
LONGTABLE = re.compile(r"\\begin\{longtable\}.*?\\end\{longtable\}", re.S)
TABLE = re.compile(r"\\begin\{tabular\}.*?\\end\{tabular\}", re.S)
LABEL = re.compile(r"\\label\{([^}]+)\}")
CITE = re.compile(r"\\cite\{([^}]+)\}")
REF = re.compile(r"\\(?:eqref|ref)\{([^}]+)\}")
BIB = re.compile(r"\\bibitem\{([^}]+)\}")


def sha(data: bytes | str) -> str:
    if isinstance(data, str):
        data = data.encode("utf-8")
    return hashlib.sha256(data).hexdigest()


def need(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def once(text: str, old: str, new: str, description: str) -> str:
    need(text.count(old) == 1, f"Expected one {description}; found {text.count(old)}")
    return text.replace(old, new, 1)


def atomic_write(path: Path, payload: bytes) -> None:
    """Use a temporary file beside the destination, then atomically replace it."""
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, filename = tempfile.mkstemp(prefix=path.name + ".", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(filename, path)
    finally:
        if os.path.exists(filename):
            os.unlink(filename)


def inventory(text: str) -> dict:
    patterns = {
        "formal_statements": FORMAL,
        "proofs": PROOF,
        "display_brackets": BRACKET_MATH,
        "display_environments": ENV_MATH,
        "witness_quote_blocks": QUOTE,
        "longtables": LONGTABLE,
        "tabular_tables": TABLE,
    }
    result = {}
    for category, pattern in patterns.items():
        records = []
        for match in pattern.finditer(text):
            records.append({
                "sha256": sha(match.group()),
                "line_start": text.count("\n", 0, match.start()) + 1,
                "line_end": text.count("\n", 0, match.end()) + 1,
                "labels": LABEL.findall(match.group()),
            })
        result[category] = records
    result["labels"] = LABEL.findall(text)
    result["citation_keys"] = [key.strip() for item in CITE.findall(text)
                               for key in item.split(",")]
    result["bibliography_keys"] = BIB.findall(text)
    result["definition_count"] = len(re.findall(r"\\begin\{definition\}", text))
    return result


def counts(records: list[dict]) -> Counter:
    return Counter(record["sha256"] for record in records)


def navigation(text: str, appendix_labels: set[str]) -> str:
    """Correct prose navigation, without modifying any protected proof or data."""
    protected = []
    for pattern in (FORMAL, PROOF, BRACKET_MATH, ENV_MATH, QUOTE, LONGTABLE, TABLE):
        protected.extend((m.start(), m.end()) for m in pattern.finditer(text))
    replacements = []
    for match in re.finditer(r"\bSection~\\ref\{([^}]+)\}", text):
        if match.group(1) in appendix_labels and not any(
                start <= match.start() < end for start, end in protected):
            replacements.append((match.start(), match.end(),
                                 match.group().replace("Section~", "Appendix~", 1)))
    for start, end, replacement in reversed(replacements):
        text = text[:start] + replacement + text[end:]
    return text


def main() -> None:
    original_bytes = REPO_PAPER.read_bytes()
    mirror_bytes = OPEN_PAPER.read_bytes()
    need(sha(original_bytes) == EXPECTED_SHA256, "Repository paper differs from frozen review source")
    need(sha(mirror_bytes) == EXPECTED_SHA256, "Open paper differs from frozen review source")
    need(original_bytes == mirror_bytes, "Open and repository paper bytes differ")
    need(BRIDGE.is_file(), "bridge-completion.json is required before this revision can run")
    bridge_bytes = BRIDGE.read_bytes()
    bridge = json.loads(bridge_bytes)
    need(bridge.get("status") == EXPECTED_BRIDGE_STATUS, "Unexpected bridge-completion status")
    need(bridge.get("initial_tree_truth_bridge_complete") is True, "Initial-tree bridge is incomplete")
    need(bridge.get("original_constructor_body_preserved") is True, "Constructor preservation is unconfirmed")
    need(bridge.get("raw_chunks") == 104 and bridge.get("tree_parts") == 104,
         "Unexpected initial-tree part count")
    need(bridge.get("existing_prefix_deductions") == 1055
         and bridge.get("existing_prefix_references") == 6006, "Unexpected checked-prefix scope")
    need(bridge.get("full_share18_replay_complete") is False
         and bridge.get("actual_share18_theorem_complete") is False
         and bridge.get("actual_share16_theorem_complete") is False,
         "Share-theorem status changed; revise the planned prose before execution")
    need(not RECEIPT.exists(), "A paper-revision receipt already exists; inspect it before rerunning")
    if BACKUP.exists():
        need(BACKUP.read_bytes() == original_bytes, "Existing original-paper backup differs")

    source = original_bytes.decode("utf-8")
    lines = source.splitlines(keepends=True)
    need(len(lines) == 6126, "Unexpected original line count")
    newline = "\r\n" if b"\r\n" in original_bytes else "\n"
    need(source.replace("\r\n", "").count("\n") == 0 if newline == "\r\n" else True,
         "Mixed line endings require review")

    def block(first: int, last: int) -> str:
        return "".join(lines[first - 1:last])

    def prose(value: str) -> str:
        return value.strip("\n").replace("\n", newline) + newline + newline

    movements = []

    def moved(name: str, first: int, last: int, destination: str,
              payload: str | None = None) -> str:
        raw = block(first, last)
        payload = raw if payload is None else payload
        movements.append({"name": name, "source_lines": [first, last],
                          "source_sha256": sha(raw), "destination": destination,
                          "_payload": payload})
        return payload

    historical_comparisons = prose(r"""
\section{Earlier fixed-graph comparison results}\label{app:historical-comparisons}
The results in this appendix retain their original graph, weight and boundary
hypotheses. They include the earlier seven-centre calculation, three
slope-and-range comparisons, coarse floor weakenings and the baseline
unsaturated-cycle obstruction. The later refined graph is treated in
Section~\ref{sec:current-limitations}.
""")
    for name, first, last in (
        ("earlier-seven-centre-model", 1778, 1796),
        ("joint-potential-optimality", 2438, 2517),
        ("coarse-short-walk-obstruction", 2583, 2625),
        ("baseline-unsaturated-obstruction", 2687, 2750),
    ):
        historical_comparisons += moved(name, first, last, "app:historical-comparisons")

    count_result = moved("completed-012310-count-theorem", 2782, 2806,
                         "sec:proved-count-refinements")
    nine_result = moved("nine-transition-exclusion", 3022, 3054,
                        "sec:proved-count-refinements")
    five_result = moved("five-count-exclusion", 3127, 3157,
                        "sec:proved-count-refinements")

    local_results = prose(r"""
\section{Further proved count restrictions}\label{sec:proved-count-refinements}
These three results hold for actual snakes without the additional count-sum
hypotheses used by the historical comparison graphs. Appendix~\ref{sec:sum-refinements}
records their effects on those graphs and the remaining conditional rules.

\subsection{Five internal counts on $012310$}
""") + count_result + prose(r"""
The theorem requires only the fitting direction window. It completes one
local premise in the comparison calculations and gives no new global bound
by itself.
""") + nine_result + newline + five_result + newline

    certificate13 = moved("historical-share13-progress", 3335, 3344,
                          "app:historical-verification-records")
    certificate18 = moved("historical-share18-progress", 3407, 3418,
                          "app:historical-verification-records")
    certificate145 = moved("historical-share145-progress", 3522, 3537,
                           "app:historical-verification-records")

    chronological = block(2751, 3345) + block(3539, 3561)
    chronological = once(chronological, block(2779, 2780), prose(r"""
The $012314$ row is Theorem~\ref{thm:outer-four-sum}. The $012310$ row is
Theorem~\ref{thm:012310-total19}, which has no additional count or parity assumptions.
"""), "count-theorem table introduction")
    chronological = once(chronological, count_result, "", "extracted count theorem")
    chronological = once(chronological, nine_result, prose(r"""
\subsection{Effect of the nine-transition exclusion}
Theorem~\ref{thm:nine-window-exclusion} gives the complete actual-snake
exclusion used in the following calculation.
"""), "extracted nine-transition theorem")
    chronological = once(chronological, five_result, prose(r"""
\subsection{Effect of the five-count exclusion}
Theorem~\ref{thm:alternate-three-four-three} gives the complete actual-snake
exclusion used in the following calculation.
"""), "extracted five-count theorem")
    chronological = once(chronological, certificate13, prose(r"""
The separate share-13 certificate and its preserved partial verification
are recorded in Appendix~\ref{app:historical-verification-records}.
"""), "relocated share13 progress")
    chronological = once(chronological, block(2813, 2814),
        "The remaining proposed restrictions have computational exclusions, while their" + newline
        + "complete Lean derivations remain unfinished. In particular, two proof-generation" + newline,
        "remaining native versus Lean status")
    chronological = once(chronological, block(3164, 3165),
        "These statements identify the deleted cycles. Appendix~\\ref{sec:zero-credit-exclusion}" + newline
        + "gives the completed zero-credit calculation for the resulting graph." + newline,
        "stale graph-minimum status")
    chronological = once(chronological, block(3332, 3333),
        "Floor $18$ remains the existing requirement in the retained conditional" + newline
        + "profile and one of its five local share targets." + newline,
        "obsolete selected-next-target prose")
    chronological = once(chronological, block(2752, 2756), prose(r"""
This appendix preserves the successive count-sum and occurrence-credit
calculations on refinements of the baseline graph. Each comparison retains
its stated local hypotheses and share profile. A completed-floor label
identifies the share inputs; several additional count restrictions remain
unproved for actual snakes. The completed local results are collected in
Section~\ref{sec:proved-count-refinements}, and the latest joint-floor
limitations are in Section~\ref{sec:current-limitations}.
"""), "historical comparison introduction")
    movements.append({"name": "count-sum-and-credit-chronology",
                      "source_lines": [[2751, 3345], [3539, 3561]],
                      "source_sha256": sha(block(2751, 3345) + block(3539, 3561)),
                      "destination": "sec:sum-refinements", "_payload": chronological,
                      "extracted_blocks": ["completed-012310-count-theorem",
                                           "nine-transition-exclusion", "five-count-exclusion",
                                           "historical-share13-progress"]})

    current = block(3346, 3538)
    current = once(current, block(3407, 3419), prose(r"""
The preserved share-18 certificate and the successive initial-database
checks are recorded in Appendix~\ref{app:historical-verification-records}.
Their current status is stated in Section~\ref{sec:verification}.
"""), "relocated share18 progress")
    current = once(current, block(3522, 3538), prose(r"""
The current certificate status is stated in Section~\ref{sec:verification}.
Appendix~\ref{app:historical-verification-records} preserves the native
certificate counts and the earlier assembly attempts.
"""), "relocated milestone145 progress")
    current = once(current, "The next experiment isolates the effect",
                   "The retained calculation isolates the effect",
                   "current comparison introduction")
    current = once(current,
                   "Combining that cycle with the preceding nine-cycle suggests testing",
                   "Combining that cycle with the nine-cycle in Appendix~\\ref{sec:share-floor-range} led to a test of",
                   "relocated nine-cycle navigation")
    current = moved("current-two-cycle-share-limitations", 3346, 3538,
                    "sec:current-limitations", current)
    current = prose(r"""
\section{Current limitations of the retained graph}\label{sec:current-limitations}
The following results concern the retained graph and the specified share
weights and occurrence event. Appendix~\ref{sec:sum-refinements} records
its inherited local hypotheses and preceding comparisons. The cycle
obstructions do not assert realizability by a complete snake. Changes to
the $012032$ floor are stated separately because they alter the eleven-cycle.
""") + current

    verification_history = prose(r"""
\section{Historical certificate and verification records}\label{app:historical-verification-records}
The following records retain the evidence and unfinished tasks at their
stated cutoffs. The later initial-database connection described in
Section~\ref{sec:verification} supersedes that specific pending status;
the earlier attempts remain part of the preserved record.

\subsection{The share-13 attempt at milestone 143}
""") + certificate13 + prose(r"""
\subsection{The share-18 certificate at milestone 144}
The following paragraph describes the milestone-144 cutoff.
""") + certificate18 + prose(r"""
\subsection{The native $012301$ replay and assembly attempt at milestone 145}
The following paragraphs describe the milestone-145 cutoff. Their
initial-database connection was subsequently completed in milestone 146;
the full local share theorems remain unfinished.
""") + certificate145 + prose(r"""
\subsection{Completed initial-database connection at milestone 146}
The original clause assignment transfers to all 104 chunks and then to the
preserved materialized initial tree. The original constructor body is
unchanged. The transfer composes with the existing prefix of 1055 deductions
using 6006 propagation references. Three checked modules supply four axiom
reports. The recorded checks use only the standard accepted axioms.
The complete share-18 replay and actual-snake interpretation remain
unfinished, as does the actual-snake share-16 theorem for $012301$
~\cite{bridge146archive}.
""")

    research_targets = prose(r"""
\section{Further conditional targets}\label{app:research-targets}
These conditional charge estimates, proposed count restrictions and
limitations retain their original hypotheses. They supply additional
research targets beyond the current conditional-234 argument.
""") + moved("longer-term-research-targets", 3604, 3642, "app:research-targets")
    construction = moved("numerical-conjecture-and-construction-criteria", 3643, 3804,
                         "before app:experiments")

    closure_opening = prose(r"""
The maintained interval is $191\le a(9)\le235$, with the contributor-proof
and independent-rebuild distinction stated in Section~\ref{sec:verification}.
The direct route to 234 requires a universal six-count floor, the stated
shortfall bound, or one of the joint count and empty-square assumptions.
The proved $0123041$ class, the $012310$ five-count theorem and the necessary
$0120324$ intervals do not establish any of those universal premises.
The separate share argument has checked graph coverage and weight
interpretation under its stated assumptions. Its remaining obligations are
as follows.
""")
    closure_joint = prose(r"""
Proposition~\ref{prop:least-floors} identifies the least sufficient integer
floors within its fixed box. The earlier slope-and-range comparisons remain
valid for their specified profiles; they do not determine the least range
for the reduced $012034$ floor 18. For the current retained graph,
Proposition~\ref{prop:two-cycle-share16-obstruction} gives a comparison of at
least $235+95/2348$ when the $012301$ and $012340$ floors are at most 16
and the eleven-cycle remains unchanged. The necessary relation is
$325F+159G>9074$. The existing $012032$ share-16 target adds 57 to the
eleven-cycle and removes the unchanged-weight hypothesis. These three
local targets therefore require a joint analysis, followed by the remaining
graph and proof obligations. Stronger geometric restrictions, boundary
accounting or conditions on actual initial and final states can change
the comparison.
""")
    verification = prose(r"""
In the newer share argument, actual windows have consistent full direction,
history and count keys. Coverage of the accepted-key graph, all 55
history-share rules, the other baseline weight components, and the boundary
and total-charge deductions have passed Lean under their stated premises.
Twenty of the 1378 reference entries have checked refutations; 1358 remain.
Exact-integer scans verify the two saved potentials on all 4947008 accepted
keys, while the complete Lean edge certificate remains unfinished.
The conditional 234 profile additionally requires share floors
$(16,18,16,16,16)$ for $012032,012034,012301,012340,012345$ and has a
strict margin of 30 at length 235 under those premises
~\cite{referenceunionarchive,potentialcertificatearchive}.

The completed actual-snake results include the sharp $012032$ pair
inequality, its equality geometry and parity consequence, the parity-free
endpoint implication, the twenty-four-window bound, the $0123041$
six-count bound, the restrictions on low-total $0120324$ windows, and the
nine-transition and five-count exclusions. The five-count sum at least 19
on $012310$ is also complete: all 1397 proof modules and their saved
dependencies have been audited. This theorem has no additional count,
endpoint-location or parity premise. The direct shortfall implication is
checked, while its sufficient universal upper bound remains unresolved
~\cite{count24archive,fivecount140archive,share145archive}.

The $012301$ share-16 target has a complete independent Boolean replay of
285541 deductions and 31017505 propagation references from 12977 original
core clauses. Its complete Lean replay, cycle-clause interpretation,
coordinate transfer and reversal remain required~\cite{share145archive}.
For the preserved $012034$ share-18 proof, the original-clause assignment
now transfers through all 104 chunks to the materialized initial tree and
composes with the checked 1055-deduction prefix using 6006 propagation
references. The original constructor body is unchanged. The preceding
assembly timeout is retained in Appendix~\ref{app:historical-verification-records}.
The remaining full replay and actual-snake interpretation are unfinished.
These records establish progress on certificates without completing either
local share theorem~\cite{bridge146archive}.

The saved-cycle obstructions concern their stated graph, weights and
occurrence event. In particular, the joint-floor obstruction leaves the
eleven-cycle unchanged, whereas the proposed $012032$ floor 16 raises its
total by 57. It therefore leaves the full conditional 234 profile
unresolved. No construction above 191 or matching optimality theorem has
been obtained. The numerical conjecture 196 is used in none of the proved
bounds. Section~\ref{sec:closure} states the remaining requirements.
""")

    edits = [
        (1778, 1796, ""), (2438, 2517, ""), (2583, 2625, ""),
        (2687, 2750, ""), (2751, 3561, local_results + current),
        (3563, 3565, closure_opening), (3591, 3598, closure_joint),
        (3604, 3804, ""), (3814, 3854, verification),
    ]
    revised = source
    for first, last, replacement in sorted(edits, reverse=True):
        revised = once(revised, block(first, last), replacement, f"original lines {first}-{last}")

    revised = once(revised, r"\appendix" + newline,
                   r"\appendix" + newline + historical_comparisons + chronological
                   + verification_history, "appendix boundary")
    experiments_heading = r"\section{Construction experiments and their scope}\label{app:experiments}"
    revised = once(revised, experiments_heading,
                   research_targets + construction + experiments_heading,
                   "construction appendix insertion")

    abstract = prose(r"""
Let $a(9)$ be the maximum edge length of an induced path in the
nine-dimensional binary hypercube. An explicit construction and an archived
contributor proof give $191\le a(9)\le235$; a complete independent rebuild
of the upper-bound proof remains pending. For a snake of length $m$, total
singleton-square count $T$ and empty-square count $s_0$, the identity
$T+2s_0+35(m+1)=9214$ supports count and share estimates. Completed local
results include the sharp pair bound eight on $012032$, its endpoint and
parity consequences, a bound of twenty-four low-pair windows, and a five-count
sum of at least nineteen on $012310$. Direct six-count and empty-square
criteria give conditional improvements to 234 and 233. A separate finite-graph
comparison reaches 234 under five unfinished share bounds and explicit
reference and potential-certificate premises. For the retained completed-share
graph, two saved cycles impose $325F+159G>9074$ on the share floors for
$012301$ and $012340$ if the eleven-cycle remains unchanged. Floors at most
sixteen leave the comparison above 235. The proposed $012032$ floor changes
that cycle, so the full conditional profile remains unresolved. The optimum
and the numerical conjecture 196 remain open.
""")
    revised = once(revised, block(39, 39), abstract, "abstract prose")
    roadmap = prose(r"""
The proof begins with the square census and the archived six-centre argument
for 235. Direct six-count criteria then state sufficient conditions for
234 and 233. Local count and endpoint theorems support the empty-square
shares and their common overlap budgets. The finite comparison graph is
treated through exact history recognition, coverage of actual state walks,
edge-weight interpretation and the boundary estimate. The conditional 234
comparison retains its five local share premises, reference refutations and
complete potential certificate. Further proved count restrictions precede
the current joint requirements on additional shares. Earlier model
calculations, construction experiments, the numerical conjecture and all
explicit witnesses are retained in the appendices.
""")
    revised = once(revised, block(86, 86), roadmap, "introduction roadmap")
    old_status_table = next(m.group() for m in TABLE.finditer(source)
                            if "Claim & Evidence and scope" in m.group())
    old_conditional_row = block(96, 96)
    new_conditional_row = (
        r"Conditional bound 234 & Slope 496, range 602 and boundary contribution 21. "
        r"Five local shares, the remaining 1358 reference refutations and the complete "
        r"finite potential certificate are still required.\\" + newline
    )
    revised = once(revised, old_conditional_row, new_conditional_row, "conditional evidence row")
    new_count_row = (
        r"Five-count sum on $012310$ & The five internal counts sum to at least 19. "
        r"All 1397 modules, including the actual-snake deduction, have completed checks; "
        r"no extra count, endpoint-location or parity premise remains.\\" + newline
    )
    revised = once(revised, block(101, 101), new_count_row + block(101, 101),
                   "completed-count evidence row insertion")

    revised = once(revised,
        "these six choices have integer means", "these six choices have means",
        "historical rational means terminology")
    revised = once(revised,
        "For the nine-transition forced-absence model, the integer mean is $9891/20$, and the potential range is 12101.",
        "For the nine-transition forced-absence model, the unscaled mean is $9891/20$; "
        "the potential certificate uses denominator 20 and scaled range 12101.",
        "denominator20 potential units")
    revised = once(revised,
        "All three final models in the comparison table have exact integer mean $18823/38$.",
        "All three final models in the comparison table have exact unscaled mean $18823/38$.",
        "denominator38 means terminology")

    target_proof_match = next(m for m in PROOF.finditer(source)
                              if r"Let $\beta_0,\ldots,\beta_{n-1}$" in m.group())
    old_proof = target_proof_match.group()
    short_path_prefix = (
        "For the first conclusion, paths with at most 242 edges already satisfy the claim; "
        "for the second, paths with at most 241 edges already satisfy it. In each remaining "
        "case all indexed internal counts below exist." + newline
    )
    new_proof = once(old_proof, r"\begin{proof}" + newline,
                     r"\begin{proof}" + newline + short_path_prefix,
                     "short-path proof prefix")
    revised = once(revised, old_proof, new_proof, "sole allowed proof edit")

    bridge_bib = prose(r"""
\bibitem{bridge146archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Original-clause truth transfer to the
preserved initial tree and checked prefix}. Research record 146,
4 November 2026. Local research record:
\path{milestones/146-initial-tree-and-paper/data/bridge-completion.json}.
The initial-database connection is complete; the full share replay and
actual-snake share theorems remain unfinished.
""")
    # The existence and completion checks above are prerequisites for this entry.
    revised = once(revised, r"\end{thebibliography}", bridge_bib + r"\end{thebibliography}",
                   "verified local milestone146 bibliography record")

    appendix_at = revised.index(r"\appendix")
    appendix_labels = set(LABEL.findall(revised[appendix_at:]))
    revised = navigation(revised, appendix_labels)
    for move in movements:
        payload = navigation(move.pop("_payload"), appendix_labels)
        need(revised.count(payload) == 1,
             f"Moved block is not present exactly once: {move['name']}")
        move["destination_sha256"] = sha(payload)
        position = revised.index(payload)
        move["destination_lines"] = [revised.count("\n", 0, position) + 1,
                                     revised.count("\n", 0, position + len(payload)) + 1]
        move["prose_adjusted"] = move["source_sha256"] != move["destination_sha256"]

    before = inventory(source)
    after = inventory(revised)
    preamble = source[:source.index(r"\begin{document}")]
    need(revised[:revised.index(r"\begin{document}")] == preamble, "Preamble changed")
    need(after["definition_count"] == before["definition_count"] == 1,
         "A named definition was added or removed")
    for category in ("formal_statements", "display_brackets", "display_environments",
                     "witness_quote_blocks", "longtables"):
        need(counts(before[category]) == counts(after[category]),
             f"Protected {category} changed, disappeared or duplicated")
    expected_proofs = counts(before["proofs"])
    expected_proofs[sha(old_proof)] -= 1
    expected_proofs[sha(new_proof)] += 1
    need(+expected_proofs == counts(after["proofs"]), "Unexpected proof change")

    new_status_table = next(m.group() for m in TABLE.finditer(revised)
                            if "Claim & Evidence and scope" in m.group())
    expected_tables = counts(before["tabular_tables"])
    expected_tables[sha(old_status_table)] -= 1
    expected_tables[sha(new_status_table)] += 1
    need(+expected_tables == counts(after["tabular_tables"]), "Unexpected table change")
    need(not (Counter(before["labels"]) - Counter(after["labels"])), "An original label disappeared")
    need(all(value == 1 for value in Counter(after["labels"]).values()), "Duplicate label")
    need(not (Counter(before["citation_keys"]) - Counter(after["citation_keys"])),
         "An original citation occurrence disappeared")
    need(not (Counter(before["bibliography_keys"]) - Counter(after["bibliography_keys"])),
         "An original bibliography entry disappeared")
    need(all(value == 1 for value in Counter(after["bibliography_keys"]).values()),
         "Duplicate bibliography key")
    need(set(REF.findall(revised)) <= set(after["labels"]), "Unresolved reference")
    need(set(after["citation_keys"]) <= set(after["bibliography_keys"]), "Unresolved citation")
    need(r"\path{milestones/146-initial-tree-and-paper/data/bridge-completion.json}" in revised,
         "Missing local bridge evidence path")

    protected_report = {
        "before": before,
        "after": after,
        "formal_statements_exact_multiset_preserved": True,
        "all_display_math_exact_multiset_preserved": True,
        "witness_quote_blocks_exact_multiset_preserved": True,
        "longtables_exact_multiset_preserved": True,
        "all_original_labels_and_citation_occurrences_preserved": True,
        "all_original_bibliography_entries_preserved": True,
        "new_named_definitions": 0,
        "allowed_proof_edit": {
            "label": "prop:window-aggregate",
            "original_lines": [4730, 4739],
            "operation": "prepend explicit trivial short-path cases after proof opening",
            "prefix": short_path_prefix,
            "before_sha256": sha(old_proof),
            "after_sha256": sha(new_proof),
        },
        "allowed_evidence_table_edit": {
            "before_sha256": sha(old_status_table), "after_sha256": sha(new_status_table),
            "changes": ["clarify conditional234 obligations", "add completed012310 count theorem"],
        },
    }
    new_bytes = revised.encode("utf-8")
    summary = {
        "status": "PASS_FULL_SOURCE_REVISION_AND_PROTECTED_CONTENT_PRESERVATION",
        "full_revision": True,
        "revision": 146,
        "source_sha256_before": EXPECTED_SHA256,
        "source_sha256_after": sha(new_bytes),
        "source_bytes_before": len(original_bytes),
        "source_bytes_after": len(new_bytes),
        "source_lines_before": len(lines),
        "source_lines_after": len(revised.splitlines()),
        "preamble_sha256_before": sha(preamble),
        "preamble_sha256_after": sha(revised[:revised.index(r"\begin{document}")]),
        "open_paper": str(OPEN_PAPER), "repository_paper": str(REPO_PAPER),
        "original_backup": str(BACKUP),
        "bridge_record": str(BRIDGE), "bridge_record_sha256": sha(bridge_bytes),
        "bridge_status": bridge["status"],
        "script_sha256": sha(Path(__file__).read_bytes()),
        "moved_blocks": movements,
        "protected_block_inventories": protected_report,
        "repeated_summary_prose_replaced": [
            {"original_lines": [39, 39], "description": "condensed abstract; mathematical results retained in body"},
            {"original_lines": [86, 86], "description": "updated roadmap"},
            {"original_lines": [3563, 3565], "description": "updated closure opening"},
            {"original_lines": [3591, 3598], "description": "current joint-floor scope replaces obsolete closure summary"},
            {"original_lines": [3814, 3854], "description": "current verification summary including146 bridge completion"},
        ],
        "original_display_math_removed": [],
        "original_display_math_moved": "All displays in moved blocks survive byte-for-byte; see block hashes and inventories.",
        "other_prose_changes": [
            "historical chronology identified by stage and exact profile",
            "extracted theorems replaced by cross-references in history",
            "stale uncomputed-minimum sentence corrected",
            "share13 and share18 progress retained at historical cutoffs",
            "rational mean terminology and scaled potential range clarified",
            "singular Section references to moved sections changed to Appendix outside protected blocks",
        ],
        "current_interval": [191, 235],
        "independent_contributor_rebuild_complete": False,
        "initial_tree_truth_bridge_complete": True,
        "full_share18_replay_complete": False,
        "actual_share18_theorem_complete": False,
        "actual_share16_theorem_complete": False,
        "conditional234_refuted": False,
        "proof_assistant_or_solver_run_by_revision_script": False,
        "compiled": False,
        "visual_PDF_checked": False,
        "new_mathematical_proof_claimed": False,
    }
    # All integrity checks finish before the first filesystem mutation.
    if not BACKUP.exists():
        atomic_write(BACKUP, original_bytes)
    need(sha(BACKUP.read_bytes()) == EXPECTED_SHA256, "Backup verification failed")
    # Respect the open editor's authoritative file, then synchronize the repository.
    atomic_write(OPEN_PAPER, new_bytes)
    atomic_write(REPO_PAPER, new_bytes)
    need(OPEN_PAPER.read_bytes() == REPO_PAPER.read_bytes() == new_bytes,
         "Post-write mirror verification failed")
    summary["open_and_repository_bytes_match"] = True
    atomic_write(RECEIPT, (json.dumps(summary, ensure_ascii=False, indent=2) + "\n").encode("utf-8"))
    print(json.dumps({"status": summary["status"], "paper_sha256": summary["source_sha256_after"],
                      "receipt": str(RECEIPT), "moved_blocks": len(movements)}, indent=2))


if __name__ == "__main__":
    main()
