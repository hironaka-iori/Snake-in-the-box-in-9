"""Merge complete, independently replayed Q6 pair catalogues."""

import argparse
from collections import Counter
import json
from pathlib import Path

from q9_three_tight_star_refine import anchor_list


REQUIRED = {"status", "catalogue_proofs", "covered_cases", "layouts", "anchor_edges"}


def catalogue_rows(source):
    return [json.loads(line) for line in source.read_text().splitlines() if line.strip()]


def audited_rows(report, source):
    data = json.loads(report.read_text().splitlines()[-1])
    if not REQUIRED <= data.keys() or data["status"] != "VERIFIED":
        return None
    e = data["anchor_edges"]
    cases = {tuple(row) for row in data["covered_cases"]}
    assert len(cases) == len(data["covered_cases"])
    assert data["catalogue_proofs"] == sum(len(anchor_list(c, e)) for c, _, _, _ in cases)
    entries = catalogue_rows(source)
    positive = Counter()
    for row in entries:
        edges = row.get("edges", (25, 25))
        c, d = row["components"]
        assert edges[0] == e and (c, edges[1], d, row["crossings"]) in cases
        positive[edges[1], d, row["crossings"]] += 1
    assert positive == dict((tuple(key), n) for key, n in data["layouts"])
    return entries


def run(directory, base, output, manifest):
    def distinct(record):
        return json.dumps(record, sort_keys=True, separators=(",", ":"))

    bank = {distinct(row) for row in catalogue_rows(base)}
    sources = []
    skipped = {}
    initial = len(bank)
    for report in sorted(directory.glob("*.replay.log")):
        catalog = report.with_suffix("").with_suffix(".verified.jsonl")
        if not catalog.is_file() or not catalog.stat().st_size:
            continue
        try:
            entries = audited_rows(report, catalog)
        except (AssertionError, ValueError, IndexError, KeyError) as error:
            skipped[str(report)] = str(error)
            continue
        if entries is not None:
            bank.update(map(distinct, entries))
            sources.append(dict(replay=str(report), catalogue=str(catalog), layouts=len(entries)))
    with output.open("x") as file:
        file.writelines(row + "\n" for row in sorted(bank))
    with manifest.open("x") as file:
        json.dump(dict(status="VERIFIED_BANK", base=str(base), sources=sources,
                       skipped=skipped, initial=initial, layouts=len(bank)), file)
    print(json.dumps(dict(status="VERIFIED_BANK", sources=len(sources),
                          skipped=len(skipped), initial=initial, layouts=len(bank))), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    for name in ("directory", "base", "output", "manifest"):
        parser.add_argument(name, type=Path)
    args = parser.parse_args()
    run(args.directory, args.base, args.output, args.manifest)
