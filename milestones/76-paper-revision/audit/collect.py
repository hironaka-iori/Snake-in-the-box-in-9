"""Pin complete manuscript coverage and read-only revision evidence."""
from pathlib import Path
import base64,datetime,hashlib,json,re
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
paper=ROOT/'paper/snake9_research.tex';raw=paper.read_bytes();lines=raw.splitlines(keepends=True)
assert sha(raw)=='d422a0b3dea2c2e81cb2d63294c14ff37b2237447faf5fca193ee2664951d341'
assert len(lines)==3317
protected={}
for name,pattern in [('author',rb'^\\author\{[^\r\n]*\}(?:\r?\n|$)'),('hypersetup',rb'^\\hypersetup\{\r?\n.*?^\}(?:\r?\n|$)')]:
    m=re.search(pattern,raw,re.M|re.S);assert m
    protected[name]=dict(sha256=sha(m.group()),base64=base64.b64encode(m.group()).decode(),text=m.group().decode('utf-8'),byte_start=m.start(),byte_end=m.end())
blocks=[dict(index=n,sha256=sha(m.group()),start_line=raw[:m.start()].count(b'\n')+1,end_line=raw[:m.end()].count(b'\n')+1) for n,m in enumerate(re.finditer(rb'\\begin\{quote\}.*?\\end\{quote\}',raw,re.S))]
coverage=dict(paper=str(paper),source_sha256=sha(raw),bytes=len(raw),lines=len(lines),coverage='All lines read, including every appendix, catalogue row, witness and bibliography item. Two truncated display gaps were reread separately.',read_ranges=[[1,430],[195,208],[431,750],[751,1120],[1121,1460],[1461,1840],[1841,2210],[2211,2557],[2558,2930],[2721,2768],[2931,3138],[3139,3317]],protected_blocks=protected,transition_quote_blocks=blocks,witness_appendix=dict(start_line=3087,end_line=3249,sha256=sha(b''.join(lines[3086:3249]))),line_endings=dict(crlf=raw.count(b'\r\n'),lf=raw.count(b'\n')))
(HERE/'source-coverage.json').write_text(json.dumps(coverage,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
paths=[f'milestones/{s}/README.md' for s in ['67-critical-family-charge','68-proof-dependency-pressure','69-count-certificate-selection','70-proof-supported-share-model','71-proved-rule-conditional-pressure','72-four-count-proof-closure','73-countfree-share-catalogue','74-graph-interpretation-audit','75-exact-history-bridge']]
paths += ['milestones/'+s for s in '''67-critical-family-charge/lean/BoundaryCharge.lean
67-critical-family-charge/data/lean-audit.json
72-four-count-proof-closure/data/proof-audit.json
72-four-count-proof-closure/critical-current/README.md
72-four-count-proof-closure/critical-current/data/source-proved-model.json
72-four-count-proof-closure/critical-current/data/countfree16-all-except012034x20-except012310x12-verification.json
72-four-count-proof-closure/critical-current/share-proof/data/proof-audit.json
73-countfree-share-catalogue/data/integration-audit.json
73-countfree-share-catalogue/data/proved-model.json
73-countfree-share-catalogue/data/assumed-012310x12-model.json
73-countfree-share-catalogue/bridge/data/accounting-audit.json
73-countfree-share-catalogue/bridge/data/proof-audit.json
73-countfree-share-catalogue/coverage/lean/SixShapeCoverage.lean
73-countfree-share-catalogue/coverage/data/proof-audit.json
73-countfree-share-catalogue/adapter/data/proof-audit.json
74-graph-interpretation-audit/optimization/README.md
74-graph-interpretation-audit/optimization/data/verification.json
74-graph-interpretation-audit/data/potential-obstruction-proof.json
74-graph-interpretation-audit/data/interface-audit.json
75-exact-history-bridge/history/data/proof-audit.json
75-exact-history-bridge/lookup/lean/GraphShareLookup.lean
75-exact-history-bridge/lookup/data/proof-audit.json
75-exact-history-bridge/numeric/lean/CountStateCode.lean
75-exact-history-bridge/numeric/data/proof-audit.json'''.splitlines()]
case_checks=[]
for c in [7300,7304,7306]:
    base=f'milestones/73-countfree-share-catalogue/cases/case{c}';receipt=read(ROOT/base/'data/proof-audit.json')
    assert receipt['status']=='PASS_LOCAL_SHARE_THEOREM';paths.append(base+'/data/proof-audit.json');checked=[]
    for module in [f'Share{c}/Geometry',f'Share{c}/Reversal',f'Share{c}/Refuted']:
        rel=base+'/lean/'+module+'.lean';actual=sha((ROOT/rel).read_bytes());assert actual==receipt['source_sha256'][module]
        checked.append(dict(source=rel,sha256=actual));paths.append(rel)
    case_checks.append(dict(case=c,status=receipt['status'],directions=receipt['directions'],share_lower=receipt['share_lower'],checked_sources=checked,limit='Prior successful receipt and named wrapper-source hashes; no new Lean replay.'))
evidence=[]
for rel in paths:
    p=ROOT/rel;assert p.is_file(),rel
    evidence.append(dict(path=rel,sha256=sha(p.read_bytes()),bytes=p.stat().st_size))
integration=read(ROOT/'milestones/73-countfree-share-catalogue/data/integration-audit.json');pending=integration['remaining_local_certificate_cases']
assert pending==[7301,7302,7303,7305,7307,7308]
assert not (ROOT/'milestones/73-countfree-share-catalogue/cases/case7305/data/proof-audit.json').exists()
out=dict(status='COMPLETE_SOURCE_READ_AND_SCOPE_AUDIT',recorded_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),paper_sha256=sha(raw),source_coverage_sha256=sha((HERE/'source-coverage.json').read_bytes()),evidence=evidence,case_source_checks=case_checks,pending_local_cases=pending,case7305_final_audit_present=False,verification_limits='Read-only source and receipt audit; no new Lean checks, graph-array replay, literature search, TeX edit or Git mutation.')
(HERE/'evidence.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
assert paper.read_bytes()==raw
print(out['status'],len(lines),'paper lines;',len(evidence),'evidence files.')
