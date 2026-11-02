"""Prepare compatible historical credit ports. No compiler is invoked.

Only import lines and the exact namespace token CountPropagation65 may change.
The latter becomes CountPropagationPort95 consistently across all generated files.
Historical receipts are evidence for the originals, not the rewritten modules.
The declaration scan is a bounded source audit, not a Lean environment check.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


PROVENANCE = "milestones/94-history-share-dispatch/data/credit-provenance.json"
PROVENANCE_SHA256 = "a04fc7d5ac70d9e751c5fe6a918efc4b1784a5292eded41da7bbdeb252e73c1e"
CURRENT_RECEIPT = "milestones/94-history-share-dispatch/data/HistoryShareAssembly-audit.json"
DEFINED_RECEIPT = "milestones/92-full-witness-batch/data/DefinedProofGraph-audit.json"
SUPPORT_MANIFEST = "milestones/87-retained-array-membership/data/RetainedPredicates-support.json"
CURRENT_ROOTS = [
    "HistoryShareAssembly", "HistoryShareCaps",
    "HistoryShareValidity", "HistoryShareCounts",
]
GENERIC = [
    (58, "ForcedShare"), (59, "ExtendedShareBridge"),
    (59, "MaskShareBridge"), (60, "GenericWindow"), (62, "SplitShare"),
    (64, "NeighbourChoice"), (65, "CountPropagation"),
    (65, "TraceShare"), (65, "CountChoice"),
]
IMPORT_LINE = re.compile(
    rb"^(?P<prefix>(?:\xef\xbb\xbf)?[ \t]*import[ \t]+)"
    rb"(?P<body>[^\r\n]*)(?P<ending>\r?\n|$)", re.M
)
IMPORT_BODY = re.compile(rb"[A-Za-z_][A-Za-z0-9_.]*(?:[ \t]+[A-Za-z_][A-Za-z0-9_.]*)*[ \t]*")
TOKEN = re.compile(rb"[A-Za-z_][A-Za-z0-9_.]*")
OLD_NAMESPACE = b"CountPropagation65"
NEW_NAMESPACE = b"CountPropagationPort95"
NAMESPACE_TOKEN = re.compile(rb"(?<![A-Za-z0-9_'])CountPropagation65(?![A-Za-z0-9_'])")


def namespace_port(data: bytes) -> bytes:
    return NAMESPACE_TOKEN.sub(NEW_NAMESPACE, data)


def ported_theorem_name(name: str) -> str:
    return namespace_port(name.encode("utf-8")).decode("utf-8")


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha(path: Path) -> str:
    return digest(path.read_bytes())


def imports(data: bytes) -> list[str]:
    result = []
    for match in IMPORT_LINE.finditer(data):
        body = match["body"]
        if not IMPORT_BODY.fullmatch(body):
            raise ValueError(f"Unsupported import syntax: {body!r}")
        result.extend(token.decode("ascii") for token in TOKEN.findall(body))
    return result


def without_imports(data: bytes) -> bytes:
    return IMPORT_LINE.sub(b"", data)


def strip_comments(text: str) -> str:
    """Remove nested Lean comments, preserving newlines for declaration scan."""
    result, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            result.extend("  ")
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            result.extend("  ")
            i += 2
        elif depth:
            result.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            result.extend(" " * (end - i))
            i = end
        else:
            result.append(text[i])
            i += 1
    if depth:
        raise ValueError("Unclosed block comment")
    return "".join(result)


def declarations(data: bytes) -> list[str]:
    """Collect explicit declaration roots, including generated-name ownership.

    Structure/inductive roots are retained: a collision in generated projection
    or constructor names then has an already colliding root. The scanner does
    not attempt to enumerate Lean-generated auxiliary declarations.
    """
    stack: list[tuple[str, str]] = []
    found = []
    text = strip_comments(data.decode("utf-8-sig"))
    for line in text.splitlines():
        match = re.match(r"^namespace\s+([A-Za-z_][\w.]*)\s*$", line)
        if match:
            stack.append(("namespace", match[1]))
            continue
        if re.match(r"^section(?:\s+\w+)?\s*$", line):
            stack.append(("section", ""))
            continue
        if re.match(r"^end(?:\s+[\w.]+)?\s*$", line):
            if stack:
                stack.pop()
            continue
        match = re.match(
            r"^(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
            r"(?:def|theorem|lemma|abbrev|structure|inductive|class|opaque|axiom)"
            r"\s+([A-Za-z_][\w.']*)", line,
        )
        if match:
            scope = ".".join(value for kind, value in stack if kind == "namespace")
            name = match[1]
            found.append(name.removeprefix("_root_.") if name.startswith("_root_.")
                         else ".".join(part for part in [scope, name] if part))
    return found


def prepare(root: Path, stage1_only: bool = False) -> dict:
    root = root.resolve()
    here = root / "milestones/95-history-credit-integration"
    relative = lambda path: path.resolve().relative_to(root).as_posix()
    provenance_path = root / PROVENANCE
    if sha(provenance_path) != PROVENANCE_SHA256:
        raise ValueError("Pinned milestone94 provenance bytes changed")
    provenance = json.loads(provenance_path.read_text(encoding="utf-8"))
    current_receipt_path = root / CURRENT_RECEIPT
    current_receipt = json.loads(current_receipt_path.read_text(encoding="utf-8"))
    if current_receipt["exit_code"] != 0:
        raise ValueError("Current import environment has no successful receipt")
    defined_receipt_path = root / DEFINED_RECEIPT
    defined_receipt = json.loads(defined_receipt_path.read_text(encoding="utf-8"))
    if defined_receipt["exit_code"] != 0:
        raise ValueError("Defined graph environment has no successful receipt")
    # This is the parent's combined checker order. In particular, the pinned
    # defined-graph paths precede remaining94 paths for LocalWindowSat ownership.
    current_paths = []
    for path in [
        here / "build", root / "milestones/94-history-share-dispatch/build",
        *map(Path, defined_receipt["paths"]), *map(Path, current_receipt["paths"]),
    ]:
        if path not in current_paths:
            current_paths.append(path)
    support_path = root / SUPPORT_MANIFEST
    support = json.loads(support_path.read_text(encoding="utf-8"))["modules"]
    source_by_object = {
        Path(row["object"]).resolve(): (Path(row["source"]), row["source_sha256"])
        for row in support.values()
    }

    def milestone(number: int) -> Path:
        matches = sorted((root / "milestones").glob(f"{number}-*"))
        if len(matches) != 1:
            raise ValueError(f"Ambiguous milestone {number}")
        return matches[0]

    def port_name(number: int, module: str) -> str:
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9]*", module):
            raise ValueError(f"Unsupported historical module name {module}")
        return f"Port95M{number}{module}"

    sources: dict[tuple[int, str], Path] = {}
    required_hashes: dict[tuple[int, str], str] = {}
    for record in provenance["modules"].values():
        key = (record["milestone"], record["module"])
        sources[key] = root / record["source"]
        required_hashes[key] = record["source_sha256"]
    for module, record in provenance["reused_geometry_modules"].items():
        key = (61, module)
        sources[key] = root / record["source"]
        required_hashes[key] = record["source_sha256"]
    for key in GENERIC:
        sources[key] = milestone(key[0]) / "lean" / f"{key[1]}.lean"

    by_name: dict[str, list[tuple[int, str]]] = {}
    for key in sources:
        by_name.setdefault(key[1], []).append(key)
    generic_by_name = {module: (number, module) for number, module in GENERIC}
    port_namespace_tokens = set()
    for source in sources.values():
        data = source.read_bytes()
        for name in declarations(data) + declarations(namespace_port(data)):
            if not name.startswith("Snake9.LocalWindow."):
                raise ValueError(f"Unexpected port declaration namespace: {name}")
            port_namespace_tokens.add(name.split(".")[2].encode("ascii"))
    dependencies: dict[tuple[int, str], list[tuple[int, str]]] = {}
    replacements = {}
    for key, path in sources.items():
        replacement, deps = {}, []
        for name in imports(path.read_bytes()):
            if name == "ShareFrame":
                replacement[name] = "LocalWindowShareBridge"
            elif name in generic_by_name:
                target = generic_by_name[name]
                replacement[name] = port_name(*target)
                deps.append(target)
            elif name.startswith("GeometryBatch"):
                target = (61, name)
                if target not in sources:
                    raise ValueError(f"Unmapped reused geometry dependency {name}")
                replacement[name] = port_name(*target)
                deps.append(target)
            elif name in by_name:
                candidates = by_name[name]
                if len(candidates) != 1:
                    raise ValueError(f"Ambiguous instance import {name}: {candidates}")
                target = candidates[0]
                replacement[name] = port_name(*target)
                deps.append(target)
            elif name not in {"Mathlib.Tactic", "LocalWindowDirBridge"}:
                raise ValueError(f"Unresolved historical import {name} in {key}")
        dependencies[key] = sorted(set(deps))
        replacements[key] = replacement

    def current_object(module: str) -> Path | None:
        suffix = Path(*module.split(".")).with_suffix(".olean")
        return next((path / suffix for path in current_paths
                     if (path / suffix).is_file()), None)

    def current_source(module: str, obj: Path) -> Path:
        if obj.resolve() in source_by_object:
            source, expected = source_by_object[obj.resolve()]
            if sha(source) != expected:
                raise ValueError(f"Pinned support source changed: {source}")
            return source
        text = obj.as_posix()
        base = Path(text.split("/build/")[0]) if "/build/" in text else obj.parent
        suffix = Path(*module.split(".")).with_suffix(".lean")
        candidates = [base / "lean" / suffix, base / "upstream" / suffix, base / suffix]
        if "/.lake/build/lib/lean/" in text:
            candidates.insert(0, Path(text.split("/.lake/build/lib/lean/")[0]) / suffix)
        for candidate in candidates:
            if candidate.is_file():
                return candidate
        raise ValueError(f"No current source for {module}: {obj}")

    current_modules, current_names = {}, {}
    pending = [*CURRENT_ROOTS, "DefinedProofGraph"]
    skipped_libraries = set()
    while pending:
        module = pending.pop()
        if module in current_modules:
            continue
        if module in {"Std", "Init", "Lean", "Mathlib"} or module.startswith(
                ("Mathlib.", "Lean.", "Std.", "Init.")):
            skipped_libraries.add(module)
            continue
        obj = current_object(module)
        if obj is None:
            raise ValueError(f"Current local import object missing: {module}")
        source = current_source(module, obj)
        data = source.read_bytes()
        relevant_namespace = any(token in data for token in port_namespace_tokens)
        names = declarations(data) if relevant_namespace else []
        for name in names:
            current_names.setdefault(name, []).append(module)
        current_modules[module] = dict(
            source=relative(source), source_sha256=sha(source),
            object=relative(obj), object_sha256=sha(obj),
            imports=imports(data), explicit_declarations=names,
            targeted_namespace_present=relevant_namespace,
        )
        pending.extend(imports(data))

    # Extract the defined-graph subclosure from the same combined traversal,
    # avoiding a second read of thousands of pinned local certificate sources.
    defined_modules = {}
    pending = ["DefinedProofGraph"]
    while pending:
        module = pending.pop()
        if module in defined_modules:
            continue
        if module in {"Std", "Init", "Lean", "Mathlib"} or module.startswith(
                ("Mathlib.", "Lean.", "Std.", "Init.")):
            skipped_libraries.add(module)
            continue
        if module not in current_modules:
            raise ValueError(f"Combined traversal omitted defined-graph import: {module}")
        defined_modules[module] = current_modules[module]
        pending.extend(current_modules[module]["imports"])

    # Stage1 may still be emitted when collisions occur only in later modules.
    # Conflicting stage2 modules are never written by this import-only generator.
    collision_rows, port_names = [], {}
    for key, source in sorted(sources.items()):
        for name in declarations(namespace_port(source.read_bytes())):
            if name in current_names:
                collision_rows.append(dict(
                    declaration=name, port=port_name(*key),
                    current_modules=current_names[name],
                ))
            if name in port_names and port_names[name] != key:
                collision_rows.append(dict(
                    declaration=name, port=port_name(*key),
                    other_port=port_name(*port_names[name]),
                ))
            port_names[name] = key

    ordered, visiting, visited = [], set(), set()

    def visit(key: tuple[int, str]) -> None:
        if key in visiting:
            raise ValueError(f"Import cycle: {key}")
        if key in visited:
            return
        visiting.add(key)
        for dependency in dependencies[key]:
            visit(dependency)
        visiting.remove(key)
        visited.add(key)
        ordered.append(key)

    visit((67, "ChargeBatch00"))
    pilot = list(ordered)
    for key in sorted(sources):
        visit(key)
    stage2 = ordered[len(pilot):]
    pilot_names = {port_name(*key) for key in pilot}
    pilot_collisions = [row for row in collision_rows if row["port"] in pilot_names]
    if pilot_collisions:
        raise ValueError("Pilot declaration collisions: " + json.dumps(pilot_collisions, indent=2))
    stage2_blocked = bool(collision_rows)
    stage1_only = stage1_only or stage2_blocked

    records, generated = {}, {}
    for key in ordered:
        number, module = key
        source = sources[key]
        data = source.read_bytes()
        original_sha = sha(source)
        if key in required_hashes and original_sha != required_hashes[key]:
            raise ValueError(f"Provenance source changed: {source}")
        base = milestone(number)
        receipt_path = base / "data/lean-audit.json"
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        if receipt["status"] != "PASS":
            raise ValueError(f"Historical audit failed: {receipt_path}")
        matches = [row for row in receipt["records"] if row["module"] == module]
        if len(matches) != 1 or matches[0]["source_sha256"] != original_sha:
            raise ValueError(f"Historical source receipt mismatch: {source}")
        build_path = base / "logs/build-record.json"
        build_record = json.loads(build_path.read_text(encoding="utf-8"))
        build_matches = [row for row in build_record["records"] if row["module"] == module]
        if (len(build_matches) != 1 or build_matches[0]["exit_code"] != 0
                or build_matches[0]["source_sha256"] != original_sha):
            raise ValueError(f"Historical build record mismatch: {source}")
        original_object = Path(build_record["build"]) / f"{module}.olean"
        if not original_object.is_file():
            raise ValueError(f"Historical object absent: {original_object}")
        edits = []

        def rewrite(match: re.Match[bytes]) -> bytes:
            line = data[:match.start()].count(b"\n") + 1
            old = match["body"]

            def rewrite_token(token_match: re.Match[bytes]) -> bytes:
                name = token_match[0].decode("ascii")
                return replacements[key].get(name, name).encode("ascii")

            new = TOKEN.sub(rewrite_token, old)
            if old != new:
                edits.append(dict(line=line, original=old.decode("ascii"),
                                  replacement=new.decode("ascii")))
            return match["prefix"] + new + match["ending"]

        import_rewritten = IMPORT_LINE.sub(rewrite, data)
        rewritten = namespace_port(import_rewritten)
        expected_non_import = namespace_port(without_imports(data))
        if expected_non_import != without_imports(rewritten):
            raise ValueError(f"Unexpected non-import byte change: {source}")
        original_names = declarations(data)
        transformed_names = declarations(rewritten)
        if [ported_theorem_name(name) for name in original_names] != transformed_names:
            raise ValueError(f"Unexpected declaration transformation: {source}")
        namespace_edits = [
            dict(original_byte_offset=match.start(),
                 line=data[:match.start()].count(b"\n") + 1,
                 original=OLD_NAMESPACE.decode("ascii"),
                 replacement=NEW_NAMESPACE.decode("ascii"))
            for match in NAMESPACE_TOKEN.finditer(data)
        ]
        destination = here / "lean" / (port_name(*key) + ".lean")
        if key in pilot and destination.exists() and destination.read_bytes() != rewritten:
            raise ValueError(f"Previously emitted stage1 source would change: {destination}")
        generated[destination] = rewritten
        records[port_name(*key)] = dict(
            original_module=module, original_milestone=number,
            original_source=relative(source), original_source_sha256=original_sha,
            original_receipt=relative(receipt_path), original_receipt_sha256=sha(receipt_path),
            original_build_record=relative(build_path), original_build_record_sha256=sha(build_path),
            original_object=relative(original_object), original_object_sha256_current=sha(original_object),
            historical_receipt_pins_object=False,
            port_source=relative(destination), port_source_sha256=digest(rewritten),
            non_import_bytes_sha256=digest(without_imports(data)),
            port_non_import_bytes_sha256=digest(without_imports(rewritten)),
            non_import_bytes_identical=without_imports(data) == without_imports(rewritten),
            decoded_non_import_text_identical=(
                without_imports(data).decode("utf-8-sig")
                == without_imports(rewritten).decode("utf-8-sig")),
            non_import_changes_only_exact_namespace_token=True,
            exact_namespace_token_replacements=namespace_edits,
            original_imports=imports(data), port_imports=imports(rewritten),
            exact_import_line_replacements=edits,
            dependencies=[port_name(*dependency) for dependency in dependencies[key]],
            external_imports=[name for name in imports(rewritten) if not name.startswith("Port95")],
            original_explicit_declarations=original_names,
            transformed_explicit_declarations=transformed_names,
            declaration_name_map=dict(zip(original_names, transformed_names)),
            stage=1 if key in pilot else 2,
        )

    selected_map = {}
    for theorem, info in provenance["theorems"].items():
        selected_map[theorem] = dict(
            ported_theorem=ported_theorem_name(theorem),
            port_module=port_name(info["milestone"], info["module"]),
            historical_source=info["source"], lower=info["lower"],
            directions=info["directions"], count_conditioned=info["count_conditioned"],
        )
    reused_map = {}
    for info in provenance["reused_geometry"]:
        module = Path(info["original_source"]).stem
        reused_map[info["original"]] = dict(
            port_module=port_name(61, module), wrapper=info["wrapper"],
            lower=info["original_lower"],
        )
    excluded_source = milestone(51) / "lean/ShareFrame.lean"
    replacement_share_source = root / current_modules["LocalWindowShareBridge"]["source"]
    plan = dict(
        status=("PREPARED_STAGE1_STAGE2_BLOCKED_BY_DECLARATIONS" if stage2_blocked
                else "PREPARED_STAGE1_ONLY_NOT_COMPILED" if stage1_only
                else "PREPARED_IMPORT_AND_NAMESPACE_PORTS_NOT_COMPILED"),
        scope="Deterministic source rewrite and bounded duplicate-name audit only.",
        generator=relative(Path(__file__)), generator_sha256=sha(Path(__file__)),
        provenance=PROVENANCE, provenance_sha256=sha(provenance_path),
        current_environment_receipt=CURRENT_RECEIPT,
        current_environment_receipt_sha256=sha(current_receipt_path),
        target_environment_paths=[str(path) for path in current_paths],
        target_environment_order="95/build,94/build,exact DefinedProofGraph92 receipt paths,remaining94 paths; duplicates removed in first-occurrence order.",
        defined_graph_environment_receipt=DEFINED_RECEIPT,
        defined_graph_environment_receipt_sha256=sha(defined_receipt_path),
        source_support_manifest=SUPPORT_MANIFEST,
        source_support_manifest_sha256=sha(support_path),
        counts=dict(port_modules=len(records), selected_theorems=len(selected_map),
                    reused_geometry_theorems=len(reused_map),
                    current_local_source_modules=len(current_modules),
                    defined_graph_local_source_modules=len(defined_modules)),
        stage1_compile_order=[port_name(*key) for key in pilot],
        stage1_scope="Minimal module closure for FamilyCharge67.G000; preserves the entire ChargeBatch00 source.",
        stage2_compile_order=[port_name(*key) for key in stage2],
        stage2_sources_written=not stage1_only,
        stage2_blocked_by_declaration_conflicts=stage2_blocked,
        total_compile_order=[port_name(*key) for key in ordered],
        modules=records, selected_theorems=selected_map,
        selected_theorem_name_map={
            theorem: info["ported_theorem"] for theorem, info in selected_map.items()
        },
        permitted_transformations=[
            "Recorded import-line module replacements.",
            "Exact namespace token CountPropagation65 becomes CountPropagationPort95.",
        ],
        reused_geometry_theorems=reused_map,
        excluded_legacy_share_frame=dict(
            source=relative(excluded_source), source_sha256=sha(excluded_source),
            replacement_import="LocalWindowShareBridge",
            replacement_source=relative(replacement_share_source),
            replacement_source_sha256=sha(replacement_share_source),
            overlapping_current_declarations=sorted(
                set(declarations(excluded_source.read_bytes()))
                & set(declarations(replacement_share_source.read_bytes()))),
            copied=False,
        ),
        duplicate_audit=dict(
            scope="Complete source-import traversal of HistoryShare94 and DefinedProofGraph92 in the combined target path order; declaration scan is restricted to files containing a port namespace token. No compiler environment inspection.",
            namespace_tokens=[token.decode("ascii") for token in sorted(port_namespace_tokens)],
            collisions=collision_rows,
            library_modules_not_source_scanned=sorted(skipped_libraries),
            generated_auxiliary_names_enumerated=False,
            current_local_modules=current_modules,
            defined_graph_local_modules=defined_modules,
        ),
        limitations=[
            "No ported module has been compiled or imported by this generator.",
            "Proof text is unchanged except imports and the exact recorded namespace token substitution; imported declaration ownership must be checked.",
            "Historical object hashes are current snapshots, not historical receipt pins.",
            "The lexical duplicate audit does not substitute for Lean elaboration and generated auxiliary-name checks.",
            "Whole original modules are preserved, so some additional local instances are also copied.",
            "No actual WordShareBound, WordCappedShareBound, maximum evaluator or graph-weight bridge is proved here.",
        ],
    )
    # All reads, pins, dependency checks and duplicate checks finish before writes.
    for destination, rewritten in generated.items():
        if stage1_only and records[destination.stem]["stage"] != 1:
            continue
        destination.parent.mkdir(parents=True, exist_ok=True)
        if not destination.exists() or destination.read_bytes() != rewritten:
            destination.write_bytes(rewritten)
    output = here / "data/port-plan.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(plan, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return plan


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[3])
    parser.add_argument("--stage1-only", action="store_true",
                        help="Write only the pilot closure; later-stage sources remain unwritten.")
    args = parser.parse_args()
    plan = prepare(args.root, args.stage1_only)
    print(json.dumps(dict(status=plan["status"], counts=plan["counts"],
                          stage1_compile_order=plan["stage1_compile_order"]), indent=2))


if __name__ == "__main__":
    main()
