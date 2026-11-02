"""Record the narrow second manuscript review; no mathematical proof replay."""
from pathlib import Path
from fractions import Fraction
import base64, datetime, hashlib, json, re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sha = lambda b: hashlib.sha256(b).hexdigest()
read = lambda p: json.loads(p.read_text(encoding="utf-8-sig"))
paper = ROOT / "paper/snake9_research.tex"
raw = paper.read_bytes()
text = raw.decode("utf-8")
old = (ROOT / "milestones/76-paper-revision/data/paper-before.tex.snapshot").read_bytes()
baseline = read(HERE / "source-coverage.json")
assert sha(old) == baseline["source_sha256"]
protected = {k: base64.b64decode(v["base64"]) in raw for k,v in baseline["protected_blocks"].items()}
assert all(protected.values())
pattern = rb"\\begin\{(theorem|proposition|lemma|corollary|conjecture|definition|remark)\}.*?\\end\{\1\}"
old_blocks = [m.group() for m in re.finditer(pattern, old, re.S)]
assert len(old_blocks) == 116 and all(block in raw for block in old_blocks)
quotes = [sha(m.group()) for m in re.finditer(rb"\\begin\{quote\}.*?\\end\{quote\}", raw, re.S)]
assert quotes == [b["sha256"] for b in baseline["transition_quote_blocks"]]
editor = Path("D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex")
assert editor.read_bytes() == raw
comparisons = [(480,536,Fraction(10609,45)), (483,551,Fraction(157625,669)), (496,600,Fraction(137941,587))]
assert all(Fraction(1098960+8*p+R, p+4200) == b for p,R,b in comparisons)
assert 1105680-4200-120*21 == 1098960
assert 227*496-111960-600 == 32
paths = [
 "milestones/76-paper-revision/text/local-catalogue.tex",
 "milestones/76-paper-revision/text/current-model.tex",
 "milestones/76-paper-revision/data/verification.json",
 "milestones/76-paper-revision/data/arithmetic-audit.json",
 "milestones/76-paper-revision/data/editor-compile.json",
 "milestones/72-four-count-proof-closure/critical-charge/share-proof/lean/Share120/Geometry.lean",
 "milestones/72-four-count-proof-closure/critical-charge/share-proof/lean/Share120/Compose.lean",
 "milestones/72-four-count-proof-closure/critical-charge/share-proof/lean/Share120/Refuted.lean",
 "milestones/72-four-count-proof-closure/critical-charge/share-proof/data/proof-audit.json",
 "milestones/72-four-count-proof-closure/critical-charge/data/share0-cap119-certificate.json",
 "milestones/72-four-count-proof-closure/critical-charge/data/witness-verification.json",
 "milestones/72-four-count-proof-closure/critical-current/data/countfree16-all-except012034x20-except012310x12-model.json",
 "milestones/72-four-count-proof-closure/critical-current/data/countfree16-all-except012034x20-except012310x12-verification.json",
 "milestones/73-countfree-share-catalogue/data/proved-model.json",
 "milestones/73-countfree-share-catalogue/data/assumed-012310x12-model.json",
 "milestones/74-graph-interpretation-audit/optimization/data/catalogue-tests.json",
 "milestones/74-graph-interpretation-audit/optimization/data/verification.json",
 "milestones/75-exact-history-bridge/history/lean/HistoryPrefix.lean",
 "milestones/75-exact-history-bridge/history/lean/ExactHistory.lean",
 "milestones/75-exact-history-bridge/history/data/proof-audit.json",
]
audit = read(ROOT / paths[8])
assert audit["status"] == "PASS_LOCAL_SHARE_THEOREM"
assert audit["bounds"] == [[4,4],[5,5],[4,4],[2,2],[6,21]] and audit["share_lower"] == 120
for module in ["Geometry", "Compose", "Refuted"]:
    p = ROOT / "milestones/72-four-count-proof-closure/critical-charge/share-proof/lean/Share120" / (module+".lean")
    assert sha(p.read_bytes()) == audit["source_sha256"]["Share120/"+module]
witness = read(ROOT / paths[10])
assert witness["counts"] == [4,5,4,2,11] and witness["total_share"] == 214
tests = read(ROOT / paths[15])["tests"]
assert len(tests) == 6
assert all([e["weight"] for e in t["cycle"]] == [616,496,376] for t in tests)
emission_scope_precise = "The history invariant, soundness of emission, absence of early emission" in text
data = dict(
 status="PASS_MATHEMATICAL_AND_SCOPE_REVIEW" if emission_scope_precise else "PASS_WITH_ONE_SCOPE_WORDING_RECOMMENDATION",
 recorded_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 paper_sha256=sha(raw), paper_lines=len(raw.splitlines()),
 scope="Complete original manuscript was read in the first audit. Second review read both complete new fragments, the revised abstract, principal-result discussion, boundary and history proofs, all current-model comparisons, closure, verification, bibliography additions and corrected historical passages. Unchanged earlier mathematics was not reread in full a second time.",
 protected_blocks=protected, old_statements_preserved=116, transition_quote_blocks_preserved=len(quotes),
 editor_identical=True, independently_recomputed_comparisons=[dict(mean=p,range=R,bound=str(b)) for p,R,b in comparisons],
 strict_margin_at_235=32, share120_source_hash_checks=True, emission_converse_scope_precise=emission_scope_precise,
 evidence=[dict(path=p,sha256=sha((ROOT/p).read_bytes())) for p in paths],
 limitations="Read-only source and archived-receipt audit, with small exact arithmetic. No Lean invocation, full certificate rebuild, graph-array replay, web research, new author-attribution claim or visual/PDF validation. Built-in preview compilation failed before compiling the source, as recorded by the parent."
)
(HERE / "second-review.json").write_text(json.dumps(data,indent=2)+"\n",encoding="utf-8")
report = f"""# Second manuscript review

Reviewed manuscript SHA256: `{sha(raw)}` ({len(raw.splitlines())} lines).

The added mathematics is consistent with the cited local results and the exact finite-model arithmetic. No substantive error was found in the new boundary argument, conditional potential criterion, history invariant or short-walk obstruction. This is a source-and-scope audit; it is not a new proof replay.

## Checked conclusions

- The graph uses five stored counts and six counts on a transition. The source/target indices, entering count at r+8, and five charged centres r+4 through r+8 agree. The nine-transition start range has m-8 terms, including the explicitly empty case m=8.
- The omitted positions are 0 through 7 and m. Endpoint contributions total eight; three adjacent internal pairs contribute twelve, and the seventh internal count contributes one. Thus the loss is exactly 21, and 1105680-4200-120*21=1098960.
- The scaled potential inequality gives the stated strict criterion 227p>111960d+R. The three displayed fractions were independently recomputed. The mixed mean 496 and range 600 have strict margin 32 at 235.
- The count-independent completed and pending rows match the recorded proof scopes. The share-120 hypotheses match the successful proof receipt and the current checked wrapper hashes. Its share-214 local witness remains clearly distinct from a complete snake.
- The longest-suffix argument is valid for a dictionary closed under deleting the final symbol. The revised emission definition makes soundness and completeness explicit. Completeness follows mathematically from maximality and listed prefix membership; the saved Lean source separately checks the invariant, emission soundness and absence of early emission, and does not contain a separately assembled converse theorem.
- The three cycle weights 616,496,376 match all six recorded obstruction tests. The short-walk algebra allows arbitrary real slopes and potentials; the cited Lean check covers rational data. The text correctly limits the finite witness checks to computation and avoids asserting actual-snake realizability.
- The closure and verification sections retain all six local share premises, the arbitrary-snake graph interpretation, lookup coverage and potential replay as outstanding. The independent rebuild limitation for the earlier 235 theorem is explicit.

## Preservation and scope

All 116 earlier statement environments remain byte-for-byte present. All eleven quoted transition blocks retain their exact hashes. The entire author line and hyperlink-setting block are byte-identical to the original audited source. The editor copy is byte-identical to the reviewed paper.

The first audit read the complete original manuscript, including every appendix. This second audit read both complete new fragments, the revised principal claims and abstract, current model, closure and verification, new bibliography entries, and the corrected historical passages. Unchanged old arguments were not reread in full a second time. The earlier three-twos printed classification remains correctly labelled as an outline.

The only review recommendation was to define emission explicitly and restrict the final Lean-check sentence to declarations actually present. Emission is now explicitly defined. Exact status of the final wording is recorded in `second-review.json`.

No new Lean or large computation was started by this audit. The parent's six arithmetic checks are cited as a separate successful check. The built-in LaTeX compiler failed while preparing its execution environment, before compiling the source; successful source and mathematical checks do not establish PDF or visual verification.

The exact reviewed source and evidence hashes are in `second-review.json`; the original complete-read evidence remains in `source-coverage.json` and `evidence.json`.
"""
(HERE / "second-review.md").write_text(report,encoding="utf-8")
assert paper.read_bytes() == raw
print(json.dumps({k:data[k] for k in ["status","paper_sha256","old_statements_preserved","transition_quote_blocks_preserved","emission_converse_scope_precise"]},indent=2))
print("report_sha256",sha((HERE/"second-review.md").read_bytes()))
print("audit_sha256",sha((HERE/"second-review.json").read_bytes()))
