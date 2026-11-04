"""Publish the completed local share-17 theorem only after its saved audit passes.

This script edits the two existing paper copies and three root research records.
It neither invokes Lean nor compiles TeX. Run the built-in document compiler
separately after this source revision. A changed input paper fails closed.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
S = R / 'milestones/154-share17-broader-semantics'
EDITOR = Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
EXPECTED_PAPER = 'b0f0519df6121e7347aadbfd70f4cde6163013ebea413c216984161fb4a1d2ce'
EXPECTED_FINAL_SOURCE = '3652fbffbd7977553308f05a744d3a0c88c3fe0ec1d2206291691e0726fe160b'
FORWARD = [[4, 4], [0, 4], [4, 4], [0, 5], [3, 3]]
REVERSE = [[3, 3], [0, 5], [4, 4], [0, 4], [4, 4]]


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def read(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))


PENDING = r'''The compact core is unchanged. Its broader clause interpretation and
transfer to arbitrary coordinates and reversed windows have now passed
Lean in 98 modules. This establishes the share-17 implication under an
explicit unsatisfiability premise for that core. The complete contradiction
replay remains unfinished, so the share-17 bound under the displayed count
hypotheses is still conditional~\cite{broader154archive}.'''

COMPLETED = r'''The compact core is unchanged. Its interpretation and coordinate and
reversal transfer have passed Lean in 98 modules. The complete 137-module
contradiction replay and the final application to actual snakes have also
passed Lean, giving the following local theorem.

\begin{theorem}[Count-conditioned share on $012032$]
\label{thm:critical-count-share17}
Let $P=(x_0,\ldots,x_m)$ be a snake in $\Q_9$, with $r+6\le m$.
Suppose that one of the following conditions holds:
\begin{enumerate}
\item The six-transition window beginning at $r$ has canonical directions
$012032$, and
\[
\alpha_{r+1}=4,\quad \alpha_{r+2}\le4,\quad
\alpha_{r+3}=4,\quad \alpha_{r+4}\le5,\quad \alpha_{r+5}=3.
\]
\item Its reversed transition sequence has canonical directions $012032$,
and the counts in the original order satisfy
\[
\alpha_{r+1}=3,\quad \alpha_{r+2}\le5,\quad
\alpha_{r+3}=4,\quad \alpha_{r+4}\le4,\quad \alpha_{r+5}=4.
\]
\end{enumerate}
Then
\[
\sum_{j=1}^{5}\sigma_{12}(x_{r+j})\ge17.
\]
\end{theorem}
\begin{proof}
The checked interpretation shows that a window satisfying either set of
hypotheses and having share sum at most 16 would satisfy the retained
11869-clause core. The complete replay derives the empty clause from
that core through 30305 deductions and 1754767 propagation references.
The checked coordinate and reversal transfer applies this contradiction
to the given snake. Since the share sum is an integer, it is at least 17.
The final composition has no remaining contradiction premise. Its saved
source, object, log and dependency records have been audited; the external
Lean and mathematics libraries remain trusted~\cite{broader154archive,share155archive}.
\end{proof}

The count hypotheses are essential to the scope of this theorem. The
universal $012032$ floor established above remains 16. The new local
theorem alone does not complete the conditional bound 234: the four
remaining share floors, reference refutations and potential certificate
listed in Section~\ref{sec:closure} remain required.'''

OLD_GRAPH = r'''If the exact-context result and its reversal are established, they raise
two edges of the eleven-cycle by one relative to the profile imposing
universal $012032$ share 16. Its total then increases from 5456 to 5458.
The fourteen-cycle remains unchanged, and this calculation alone gives
no improved global bound~\cite{critical153archive}.'''

NEW_GRAPH = r'''Assigning the proved exact-context result and its reversal as additional
floors raises two edges of the saved eleven-cycle by one relative to the
profile imposing universal $012032$ share 16. Its total increases from
5456 to 5458. The fourteen-cycle remains unchanged. This is a calculation
for the saved graph and weights; it supplies neither a potential on every
edge nor an improved global bound~\cite{critical153archive,share155archive}.'''

BIB = r'''\bibitem{share155archive}
I.~Hironaka, T.~Ma, and S.~Zhan, \emph{Complete contradiction replay and
count-conditioned critical-window share theorem}, research archive,
milestone 155.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/155-share17-replay}.

'''

ROOT_UPDATE = r'''# Research update: count-conditioned share-17 theorem checked

The complete 137-module contradiction replay and its application to actual
snakes have passed Lean. The replay covers 30,305 deductions and 1,754,767
propagation references, with 407 axiom reports; the broader interpretation
and transfer use 98 checked modules with 100 axiom reports. The final
composition has one further axiom report and no contradiction premise.

For a fitting six-transition window with forward canonical directions
012032, the five counts must satisfy (4, at most 4, 4, at most 5, 3).
For reversed canonical directions 012032, their original-order conditions
are (3, at most 5, 4, at most 4, 4). Under either condition, the five-centre
share at resolution 12 is at least 17. These count hypotheses remain.
The universal 012032 floor is 16; a universal floor 17 is not asserted.

Read milestones/155-share17-replay/COMPLETION.md and its saved actual-snake
audit. The two matching eleven-cycle edges receive one extra unit each
relative to the universal-floor-16 profile, raising its saved total from
5456 to 5458. This does not provide a new potential or global bound.
The conditional 234 comparison still requires its four other local floors,
reference refutations and complete potential certificate. The maintained
191--235 interval retains its contributor-proof and independent-rebuild
distinction. Both existing paper sources now state the local theorem;
their document compilation is a separate pending check. Last full paper
revision: 146; next: 156. This is a narrow completion update.

Historical updates follow; their pending statuses describe earlier stages.

'''

COMPLETION_DOCUMENT = r'''# Count-conditioned critical-window share theorem

The final saved-evidence audit has passed. For any snake
\(P=(x_0,\ldots,x_m)\) in \(Q_9\), consider a six-transition window
with \(r+6\le m\). Either of the following is sufficient:

1. Its forward canonical directions are 012032 and
   \(\alpha_{r+1}=4,\ \alpha_{r+2}\le4,\ \alpha_{r+3}=4,
   \ \alpha_{r+4}\le5,\ \alpha_{r+5}=3\).
2. Its reversed transition sequence has canonical directions 012032 and
   the counts in the original order satisfy
   \(\alpha_{r+1}=3,\ \alpha_{r+2}\le5,\ \alpha_{r+3}=4,
   \ \alpha_{r+4}\le4,\ \alpha_{r+5}=4\).

Then \(\sum_{j=1}^{5}\sigma_{12}(x_{r+j})\ge17\).
The count conditions remain; no separate contradiction premise remains.
The universal 012032 floor established in milestone 152 remains 16.

The checked evidence consists of:

- 98 interpretation and coordinate/reversal-transfer modules, with 100
  axiom reports, recorded in milestone 154's semantics-completion.json.
- 137 complete contradiction-replay modules, including the 34 accepted
  pilot modules, with 407 axiom reports. The same 11,869-clause core yields
  the empty clause after 30,305 deductions and 1,754,767 references.
- One final actual-snake composition and its axiom report. The auditor
  checks its exact hypotheses, the forward and reverse count order,
  sources, compiled objects, logs, checker identities and dependencies.
  Only the permitted standard axioms occur in these reports. The external
  Lean and mathematics libraries remain trusted.

The authoritative completion record is data/actual-snake-completion.json.
The existing scripts/audit_actual.py --verify-only command rechecks its
saved evidence without compiling Lean. Earlier pilot and preparation
records retain their original bytes and describe earlier stages.

For the saved retained graph, broadening the count conditions adds no
matching rows: its pair-sum condition already forces the relaxed counts
back to 4 and 5. Applying the proved floor to the two matching eleven-cycle
edges raises its saved total from 5456 to 5458 relative to the universal
012032-floor-16 profile. The fourteen-cycle has no matching edge.
This calculation does not certify a potential on the entire graph.

No new global bound follows from this milestone. In particular, the
conditional 234 comparison still needs local floors (18,16,16,16) for
012034, 012301, 012340 and 012345, their required interpretation and
reversal, reference refutations and a complete potential certificate.
The maintained 191--235 interval retains the paper's distinction between
the contributor upper-bound proof and its pending independent rebuild.
The next useful step on this route is to include the proved local floor
in the graph weights and seek an improved potential, keeping the full
edge verification and boundary accounting as explicit obligations.

The two existing paper sources have been updated in place with identical
bytes. Authors, preamble and local hyperref settings are preserved. The
revision record data/paper-revision.json gives input/output hashes and
backups. This source update performs no TeX compilation and asserts no
new PDF check. The last full paper rewrite remains 146 and the next is 156.
'''


def main():
    require(__debug__, 'Run without Python optimization; the evidence auditor uses assertions.')
    actual_path = H / 'data/actual-snake-completion.json'
    require(actual_path.exists(), 'Waiting for the completed actual-snake audit; no documents changed.')
    actual_raw = actual_path.read_bytes()
    actual = json.loads(actual_raw)
    require(actual['status'] == 'PASS_ACTUAL_SNAKE_SHARE17_WITH_COUNT_CONDITIONS',
            'The final actual-snake audit has not passed.')
    required = dict(actual_snake_composition_complete=True,
                    shared_core_contradiction_complete=True, semantic_modules=98,
                    replay_modules=137, directions=[0, 1, 2, 0, 3, 2], bounds=FORWARD,
                    reverse_bounds=REVERSE, resolution=12, share_lower_bound=17,
                    count_conditions_retained=True, reversal_included=True,
                    extra_unsat_premise=False, universal_012032_share17=False,
                    new_global_upper_bound=False)
    for key, value in required.items():
        require(actual.get(key) == value, f'Unexpected final scope: {key}')
    require(digest((H / 'lean/ShareComplete155.lean').read_bytes()) == EXPECTED_FINAL_SOURCE,
            'Final theorem source changed.')
    auditor = H / 'scripts/audit_actual.py'
    require(actual['source_files_sha256'].get(auditor.relative_to(R).as_posix())
            == digest(auditor.read_bytes()), 'The accepted auditor changed.')
    result = subprocess.run([sys.executable, '-B', '-X', 'utf8', str(auditor), '--verify-only'],
                            cwd=R, capture_output=True, text=True, encoding='utf-8')
    require(result.returncode == 0, 'Saved-evidence verification failed: ' + result.stdout + result.stderr)
    require(json.loads(result.stdout) == actual, 'The verified final record changed.')
    require(actual_path.read_bytes() == actual_raw, 'Final audit record changed during verification.')
    full_path = H / 'data/full-replay-completion.json'
    sem_path = S / 'data/semantics-completion.json'
    full, sem = read(full_path), read(sem_path)
    require(full['status'] == 'PASS_COMPLETE_SHARED_SHARE17_CORE_CONTRADICTION'
            and (full['checked_modules'], full['axiom_reports'], full['deductions'], full['references'])
            == (137, 407, 30305, 1754767), 'Unexpected complete replay evidence.')
    require(sem['status'] == 'PASS_BROADER_CORE_SEMANTICS_AND_CONDITIONAL_ACTUAL_SNAKE_SHARE17'
            and (sem['checked_modules'], sem['axiom_reports']) == (98, 100),
            'Unexpected interpretation evidence.')

    paper = R / 'paper/snake9_research.tex'
    raw = paper.read_bytes()
    require(raw == EDITOR.read_bytes(), 'The paper copies differ; no documents changed.')
    require(digest(raw) == EXPECTED_PAPER, 'The paper changed after updater preparation; review the new text.')
    old = raw.decode('utf-8')
    new = old
    changes = []
    for before, after in [(PENDING, COMPLETED), (OLD_GRAPH, NEW_GRAPH),
                          (r'\end{thebibliography}', BIB + r'\end{thebibliography}')]:
        require(new.count(before) == 1, 'Expected exactly one revision passage: ' + before[:80])
        new = new.replace(before, after)
        changes.append(dict(before=before, after=after))
    preamble = old.split(r'\begin{document}', 1)[0]
    require(new.split(r'\begin{document}', 1)[0] == preamble, 'Preamble changed.')
    require(new.count(r'\begin{definition}') == old.count(r'\begin{definition}'), 'Definition count changed.')
    require('.lean' not in new and 'Snake9.' not in new, 'Implementation identifier entered the paper.')
    require(new.count(r'\label{thm:critical-count-share17}') == 1, 'Duplicate local theorem label.')
    require(new.count(r'\bibitem{share155archive}') == 1, 'Duplicate archive citation.')
    output = new.encode('utf-8')

    # Construct and validate every requested mutation before writing any document.
    mutations = [(paper, raw, output), (EDITOR, raw, output)]
    for name in ['README.md', 'RESEARCH_LEDGER.md', 'COLLABORATION.md']:
        path = R / name
        before = path.read_bytes()
        require(ROOT_UPDATE.splitlines()[0].encode('utf-8') not in before, 'Completion already recorded: ' + name)
        require(not before.startswith(b'\xef\xbb\xbf'), 'Review BOM before prepending: ' + name)
        mutations.append((path, before, ROOT_UPDATE.encode('utf-8') + before))
    completion = H / 'COMPLETION.md'
    record_path = H / 'data/paper-revision.json'
    backup_dir = H / 'audit/document-before155'
    require(not completion.exists(), 'COMPLETION.md already exists; preserve it.')
    require(not record_path.exists(), 'The paper revision has already been recorded.')
    require(not backup_dir.exists(), 'Document backup directory already exists; review before retrying.')
    mutations.append((completion, None, (COMPLETION_DOCUMENT + '\n').encode('utf-8')))
    backup_names = ['repo-paper.tex.txt', 'editor-paper.tex.txt', 'README.md.txt',
                    'RESEARCH_LEDGER.md.txt', 'COLLABORATION.md.txt']
    records = []
    for index, (path, before, after) in enumerate(mutations):
        records.append(dict(path=str(path), sha256_before=digest(before) if before is not None else None,
                            sha256_after=digest(after), backup=str(backup_dir / backup_names[index])
                            if before is not None else None))
    record = dict(status='SOURCE_UPDATED_AFTER_ACCEPTED_LOCAL_SHARE17_THEOREM',
                  timestamp_utc=datetime.now(timezone.utc).isoformat(),
                  source_sha256_before=digest(raw), source_sha256_after=digest(output),
                  author_preamble_hypersetup_unchanged=True, preamble_sha256=digest(preamble.encode('utf-8')),
                  new_definitions=0, local_theorem_complete=True, count_conditions_retained=True,
                  new_global_upper_bound=False, universal_012032_share17=False,
                  conditional234_obligations_retained=True, last_full_revision=146, next_full_revision=156,
                  tex_compilation_performed=False, pdf_check_status='PENDING_SEPARATE_DOCUMENT_COMPILATION',
                  prose_replacements=changes, documents=records,
                  evidence_sha256={str(path): digest(path.read_bytes()) for path in
                      [actual_path, full_path, sem_path, auditor, Path(__file__)]})
    # Recheck current document bytes immediately before making backups and edits.
    for path, before, _ in mutations:
        require((path.read_bytes() == before) if before is not None else not path.exists(),
                'Document changed while preparing revision: ' + str(path))
    backup_dir.mkdir(parents=True)
    for index, (_, before, _) in enumerate(mutations):
        if before is not None:
            (backup_dir / backup_names[index]).write_bytes(before)
    written = []
    try:
        for path, before, after in mutations:
            path.write_bytes(after)
            written.append((path, before))
            require(path.read_bytes() == after, 'Document write verification failed: ' + str(path))
        record_path.write_bytes((json.dumps(record, indent=2) + '\n').encode('utf-8'))
    except BaseException:
        # Restore only files this execution actually changed. Preserve all backups.
        for path, before in reversed(written):
            if before is None:
                path.unlink(missing_ok=True)
            else:
                path.write_bytes(before)
        raise
    print(json.dumps({key: record[key] for key in ['status', 'source_sha256_before',
        'source_sha256_after', 'new_global_upper_bound', 'tex_compilation_performed', 'pdf_check_status']}))


if __name__ == '__main__':
    main()
