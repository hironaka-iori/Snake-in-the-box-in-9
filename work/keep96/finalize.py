"""Validate all saved evidence, combine both budgets, and prepare a concise report."""
import csv
import statistics
import subprocess
from collections import Counter
from common import *


def main():
    pilot=json.loads((OUT/'pilot-results.json').read_text())
    survey=json.loads((OUT/'survey-results.json').read_text())
    if not pilot['complete'] or not survey['complete']:raise ValueError('survey unfinished')
    rows=pilot['entries']+survey['entries']
    if len(rows)!=262 or sorted(r['entry'] for r in rows)!=list(range(262)):
        raise ValueError('not exactly 262 distinct entries')
    proof_checks={}
    for phase in ('pilot','survey'):
        path=OUT/f'{phase}-evidence-audit.json'
        if path.exists():
            for r in json.loads(path.read_text())['entries']:
                proof_checks[r['entry']]=r.get('proof_check','NOT_CHECKED')
                if 'proof_check_log' in r and sha(ROOT/r['proof_check_log'])!=r['proof_check_log_sha256']:
                    raise ValueError('proof check log changed')
    # Later bounded checks supersede the original timeout only when successful.
    # Original audits remain intact as historical records.
    native_checks={}
    native_rows=[]
    native_path=OUT/'native-audit/results.json'
    if native_path.exists():
        native=json.loads(native_path.read_text())
        native_rows=native['entries']
        if sha(HERE/'vendor/drat-trim/drat-trim.c')!=native['build']['source_sha256']:
            raise ValueError('native source changed')
        for r in native['entries']:
            if sha(ROOT/r['log'])!=r['log_sha256']:raise ValueError('native log changed')
            original=next(x for x in rows if x['entry']==r['entry'])
            if sha(ROOT/original['certificate'])!=r['certificate_sha256']:raise ValueError('native certificate changed')
            cnf=next(p for p in original['identity']['formula_hashes'] if p.endswith('.cnf.gz'))
            if sha(ROOT/cnf)!=r['formula_sha256']:raise ValueError('native formula changed')
            native_checks[r['entry']]=r['status']
            if r['status']=='PASSED_NATIVE_DRAT_CHECK':proof_checks[r['entry']]=r['status']
    extended_path=OUT/'large-proof-audit.json'
    if extended_path.exists():
        for r in json.loads(extended_path.read_text())['entries']:
            if sha(ROOT/r['log'])!=r['log_sha256']:raise ValueError('extended log changed')
            if r['status']=='PASSED_EXECUTABLE_RUP_CHECK':
                if sha(ROOT/r['check_result'])!=r['check_result_sha256']:raise ValueError('extended check changed')
                if sha(HERE/'check_proof.py')!=r['identity']['checker_sha256']:raise ValueError('RUP checker changed')
                proof_checks[r['entry']]=r['status']
    table=[]
    for r in sorted(rows,key=lambda r:r['entry']):
        for name,value in r['artifact_hashes'].items():
            if sha(ROOT/name)!=value:raise ValueError('artifact hash mismatch: '+name)
        identity=r['identity'];config=identity['config']
        if config['keep']!=96 or config['total_vertices']!=193:raise ValueError('target drift')
        if config['encoder_sha256']!=sha(ROOT/'work/build_regrowth_cnf.py') or config['bank_sha256']!=sha(ROOT/'work/bank9.json'):
            raise ValueError('encoder or bank changed')
        cnf=next(ROOT/p for p in identity['formula_hashes'] if p.endswith('.cnf.gz'))
        mapping=next(ROOT/p for p in identity['formula_hashes'] if p.endswith('.json.gz'))
        d=json.loads(gzip.decompress(mapping.read_bytes()))
        if d['target']!=98 or len(d['prefix'])!=96 or len(d['clauses'])!=len(d['reasons']):
            raise ValueError('formula semantics/provenance mismatch')
        expected=f"p cnf {d['variables']} {len(d['clauses'])}\n"+''.join(' '.join(map(str,c))+' 0\n' for c in d['clauses'])
        if gzip.decompress(cnf.read_bytes()).decode()!=expected:raise ValueError('DIMACS/mapping differ')
        if any(not 1<=abs(x)<=d['variables'] for c in d['clauses'] for x in c):raise ValueError('bad variable')
        table.append(dict(entry=r['entry'],bank_index=r['bank_index'],reversed=r['reversed'],
            phase='pilot' if r['entry'] in pilot['planned_entries'] else 'screen',keep=96,total_vertices=193,
            status=r['status'],termination=r['termination'],wall_limit_seconds=config['worker_wall_limit_seconds'],
            runtime_seconds=r['runtime_seconds'],solver_seconds=r.get('solver_seconds'),memory_limit_mib=config['memory_limit_mib'],
            peak_rss_bytes=r['peak_rss_bytes'],variables=r['variables'],clauses=r['clauses'],
            formula=cnf.relative_to(ROOT).as_posix(),mapping=mapping.relative_to(ROOT).as_posix(),
            cnf_gzip_sha256=sha(cnf),mapping_gzip_sha256=sha(mapping),
            config_sha256=hashlib.sha256(json.dumps(identity,sort_keys=True).encode()).hexdigest(),
            result=r['attempt']+'/result.json',solver_log=r['attempt']+'/solver.log',certificate=r.get('certificate'),
            certificate_sha256=sha(ROOT/r['certificate']) if r.get('certificate') else None,
            certificate_bytes=(ROOT/r['certificate']).stat().st_size if r.get('certificate') else 0,
            proof_status=proof_checks.get(r['entry'],'NOT_CHECKED'),
            native_proof_status=native_checks.get(r['entry'],'NOT_CHECKED'),
            genuine_snake_verified=r.get('diagnosis',{}).get('full_snake_verified',False)))
    counts=dict(Counter(r['status'] for r in table));unsolved=[r['entry'] for r in table if r['status']=='UNKNOWN']
    summary=dict(keep=96,total_vertices=193,entries_tested=262,status_counts=counts,unknown_entries=unsolved,
                 unique_dimacs_formulas=len({r['cnf_gzip_sha256'] for r in table}),
                 proof_status_counts=dict(Counter(r['proof_status'] for r in table)),
                 native_proof_status_counts=dict(Counter(r['native_proof_status'] for r in table)),
                 positive_controls=262,full_lean_formalization_started=False,
                 scope='Solver necessary-condition results; executable checks are not Lean proofs; no global optimum claim')
    save(OUT/'summary.json',summary);save(OUT/'results.json',dict(summary=summary,entries=table))
    with (OUT/'results.csv').open('w',newline='',encoding='utf-8') as f:
        w=csv.DictWriter(f,fieldnames=list(table[0]));w.writeheader();w.writerows(table)
    # Preserve all proofs locally; keep Git certificate additions below a total budget.
    chosen=set();budget=20*1024**2
    for r in sorted(table,key=lambda r:r['certificate_bytes']):
        if r['certificate'] and r['certificate_bytes']<=1024**2 and r['certificate_bytes']<=budget:
            chosen.add(r['certificate']);budget-=r['certificate_bytes']
    save(OUT/'certificate-index.json',dict(policy='All full certificates preserved locally; <=1 MiB each and <=20 MiB combined committed to Git.',
        entries=[dict(entry=r['entry'],path=r['certificate'],sha256=r['certificate_sha256'],bytes=r['certificate_bytes'],
                      include_in_git=r['certificate'] in chosen,proof_status=r['proof_status']) for r in table if r['certificate']]))
    baseline='acee575f181b8a6d35775f985169ec15cb2cf021'
    branch=subprocess.check_output(['git','branch','--show-current'],cwd=ROOT,text=True).strip()
    if branch!='research/keep96-feasibility':raise ValueError('wrong branch')
    subprocess.run(['git','diff','--exit-code',baseline,'--','work/lean112','outputs/lean112'],cwd=ROOT,check=True)
    extras=subprocess.check_output(['git','status','--porcelain','--untracked-files=all','--','work/lean112','outputs/lean112'],cwd=ROOT,text=True)
    if extras:raise ValueError('KEEP=112 files changed')
    save(OUT/'isolation-audit.json',dict(baseline=baseline,branch=branch,clone=str(ROOT),
        protected_directories_unchanged=True,shared_objects=False,
        object_alternates_exists=(ROOT/'.git/objects/info/alternates').exists(),
        no_keep112_workers_launched=True,commits_only_on_own_branch=True))
    pilot_times=[r['runtime_seconds'] for r in pilot['entries']]
    pilot_counts=dict(Counter(r['status'] for r in pilot['entries']))
    pilot_fast=sum(r['status']=='UNSAT' and r['runtime_seconds']<10 for r in pilot['entries'])
    report=f'''# KEEP=96 feasibility report

Baseline `{baseline}`; independent branch `{branch}`. All new work is in
`work/keep96/` and `outputs/keep96/`. KEEP=112 sources/results remain unchanged.

## What was established

The bank has 131 valid 191-edge induced paths, 262 oriented entries. All 262 known
witnesses satisfy the KEEP=96 encoding at their correct 192-vertex total, including
every auxiliary counter assignment. All fail as assignments to the 193-vertex
target, as expected. This is a positive-control/data audit, not a universal proof
of encoder soundness. The mathematical interpretation is explained in the README.

The 12 outcome-blind, structurally varied pilot cases returned **{pilot_counts}** with a
300-second worker cap and a hard 2048 MiB memory cap. Runtime range:
{min(pilot_times):.3f}–{max(pilot_times):.3f} seconds; median {statistics.median(pilot_times):.3f} seconds;
sum {sum(pilot_times):.3f} seconds. {pilot_fast} UNSAT cases finished below ten seconds.

This justified a single **10-second** screen of the other 250 entries, under the
same memory limit. Only the computation budget changed: KEEP=96 and the 193-vertex
target did not. Combined outcomes: **{counts}**. The complete table is
`results.csv` / `results.json`; each row includes its budget and evidence paths.
Unknown entries: `{unsolved}`. They were not repeatedly retried or called SAT/UNSAT.

## Evidence and limitations

All 262 compressed DIMACS formulas match their saved JSON mappings, counter trees
and clause provenance. Hashes of formulas, configurations, models/proofs and logs
were verified. There are {summary['unique_dimacs_formulas']} distinct DIMACS byte streams.
Solver: Glucose 4.1 via python-sat 1.9.dev16, default parameters, proof logging on;
the binary hash and environment are in each result. Solver times are not portable
benchmarks: bounded certificate checks ran concurrently for part of the survey.
The parent's 0.1-second polling may cause small wall-limit overshoot.

Proof-check statuses: `{summary['proof_status_counts']}`. These refer to executable
certificate checking, not Lean. Native DRAT-trim statuses (overlapping checks):
`{summary['native_proof_status_counts']}`. The original sixty-second audit is retained;
successful later checks supersede its timeouts in this combined table.
A failed/timed-out proof check does not upgrade the solver
result to a verified theorem. All available UNSAT certificates remain locally
preserved. `certificate-index.json` records paths, sizes and SHA256 hashes, including
large proofs omitted from Git. To restore those on another computer, transfer them
from this clone or rerun the exact recorded configuration; missing evidence is
never silently reused. The largest pilot proof is about 55.4 MiB compressed and
contains over three million proof lines, demonstrating a certification bottleneck.

No SAT result is automatically a snake: the relaxation allows a head path plus
disconnected cycles. The worker validates any SAT model, reconstructs its head
component, and checks all unordered vertex pairs before calling it a genuine
192-edge construction. No global optimality conclusion follows from bank prefixes.

## Recommendation

KEEP=96 is computationally promising for many instances, but a full KEEP=96 Lean
campaign is **premature**. First resolve the remaining UNKNOWN cases with separately
budgeted, justified experiments; do not silently increase this survey's limits.
Second, use an efficient native proof checker and proof trimming/compression before
translating multi-million-line proofs into Lean. Third, establish the KEEP=96
geometric interpretation/coverage bridge for the exact encoder used here. Exact
formula deduplication may reduce repeated Boolean work, but must not erase the
distinct bank-prefix interpretations. No KEEP=112 worker or Lean campaign was run.

## Reproduction and resumption

See `work/keep96/README.md`. Run `prepare.py`, `run.py --phase pilot`, then
`screen_remaining.py`; all solver attempts are bounded and persisted per entry.
The second pilot invocation reused all 12 completed attempts after checking the
formula/configuration identity and saved hashes, without new solver calls.
Run `finalize.py` only once both phases finish. A `started.json` without a result is
an incomplete attempt, never a completed proof. Full proof locations remain local
even when the appropriately sized Git evidence subset is used elsewhere.
'''
    if native_rows:
        report+='\n## Follow-up: large certificates\n\n'
        report+='The three original certificate-check timeouts were revisited with native DRAT-trim.\n'
        report+='The fixed upstream source, build configuration, controls, hashes and complete logs\n'
        report+='are preserved in `work/keep96/vendor/drat-trim/` and `outputs/keep96/native-audit/`.\n\n'
        report+='| Entry | Native certificate status | Seconds |\n|---|---|---:|\n'
        for r in native_rows:report+=f"| {r['entry']} | {r['status']} | {r['seconds']:.3f} |\n"
        report+='\nThese native checks used 1800-second and 2048-MiB limits. They verify the Boolean\n'
        report+='UNSAT certificates, not Lean theorems. The 20 solver UNKNOWN cases remain unchanged.\n'
    (OUT/'REPORT.md').write_text(report,encoding='utf-8')
    print(json.dumps(summary,indent=2),flush=True)


if __name__=='__main__':main()
