"""Emit small literal crossing-allocation facts; never invoke Lean."""
from pathlib import Path
import hashlib
import json

H = Path(__file__).resolve().parents[1]
EXPECTED = {
    "regions45.json": "e64a1de95fe6354ec64e8a5bfc51457bafc262f581df1188a1683978c26d5bb9",
    "lower-pairs.json": "36db50e0498768de092cbb2528bf32488f1133c0f591702462bcf1ab52621a88",
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    inputs = {}
    pins = {}
    for name, expected in EXPECTED.items():
        path = H / "data" / name
        actual = sha(path)
        if actual != expected:
            raise ValueError(f"Pinned input changed: {name}")
        pins[str(path)] = actual
        inputs[name] = json.loads(path.read_bytes())
    raw = inputs["regions45.json"]
    reduced = inputs["lower-pairs.json"]
    ids = [entry["context"] for entry in reduced["contexts"]]
    if len(ids) != 154 or len(set(ids)) != 154:
        raise ValueError("The expected 154 distinct reduced contexts changed.")
    rows = []
    for entry in reduced["contexts"]:
        ident = entry["context"]
        context = raw["contexts"][ident]
        if context["id"] != ident:
            raise ValueError("Context index differs from its identifier.")
        data = dict(context=ident, budget=context["replacement_crossings"])
        face_counts = []
        for name, part in zip(("first", "second"), context["parts"]):
            start, finish = part["anchors"]
            start_upper, finish_upper = start >= 256, finish >= 256
            same_face_count = sum((v >= 256) == start_upper for v in part["allowed"])
            face_counts.append(same_face_count)
            data[name + "Parity"] = int(start_upper != finish_upper)
            data[name + "ZeroAllowed"] = same_face_count >= raw["width"] + 1
            data[name + "Desired"] = int(start_upper) + int(finish_upper)
        if entry["allocations"] != [[data["firstDesired"], data["secondDesired"]]]:
            raise ValueError("Stored allocation differs from its desired upper-anchor count.")
        rows.append(dict(fields=data, same_start_face_counts=face_counts))

    source = r'''import Std

set_option Elab.async false
set_option maxRecDepth 4096

namespace AllocationFacts228

-- Literal extraction and face-capacity inputs are native, pinned separately.
-- This module checks only the resulting finite allocation arithmetic.
structure AllocationRow where
  context : Nat
  budget : Nat
  firstParity : Nat
  secondParity : Nat
  firstZeroAllowed : Bool
  secondZeroAllowed : Bool
  firstDesired : Nat
  secondDesired : Nat

def rows : List AllocationRow := [
'''
    for index, row in enumerate(rows):
        fields = []
        for key, value in row["fields"].items():
            literal = str(value).lower() if isinstance(value, bool) else str(value)
            fields.append(f"{key} := {literal}")
        source += "  { " + ", ".join(fields) + " }" + ("," if index + 1 < len(rows) else "") + "\n"
    source += r''']

def checkRow (r : AllocationRow) : Bool :=
  (List.range (r.budget + 1)).all fun a =>
    (List.range (r.budget + 1)).all fun b =>
      decide ((a + b = r.budget ∧
        a % 2 = r.firstParity ∧ b % 2 = r.secondParity ∧
        (a = 0 → r.firstZeroAllowed = true) ∧
        (b = 0 → r.secondZeroAllowed = true)) →
        a = r.firstDesired ∧ b = r.secondDesired)

theorem row_count : rows.length = 154 := by decide

theorem all_allocations : rows.all checkRow = true := by decide

/-- Nonnegative crossing counts satisfying the pinned budget, parity and
zero-count permissions have the listed allocation. Actual-path parity and
face-capacity implications must be supplied separately. -/
theorem forced_allocation (r : AllocationRow) (hr : r ∈ rows)
    (a b : Nat) (hsum : a + b = r.budget)
    (hfirst : a % 2 = r.firstParity)
    (hsecond : b % 2 = r.secondParity)
    (hzeroFirst : a = 0 → r.firstZeroAllowed = true)
    (hzeroSecond : b = 0 → r.secondZeroAllowed = true) :
    a = r.firstDesired ∧ b = r.secondDesired := by
  have hrow := List.all_eq_true.mp all_allocations r hr
  change (List.range (r.budget + 1)).all (fun a =>
    (List.range (r.budget + 1)).all (fun b =>
      decide ((a + b = r.budget ∧
        a % 2 = r.firstParity ∧ b % 2 = r.secondParity ∧
        (a = 0 → r.firstZeroAllowed = true) ∧
        (b = 0 → r.secondZeroAllowed = true)) →
        a = r.firstDesired ∧ b = r.secondDesired))) = true at hrow
  have ha : a ∈ List.range (r.budget + 1) := List.mem_range.mpr (by omega)
  have hb : b ∈ List.range (r.budget + 1) := List.mem_range.mpr (by omega)
  have hpair := List.all_eq_true.mp (List.all_eq_true.mp hrow a ha) b hb
  have hforced :
      (a + b = r.budget ∧
        a % 2 = r.firstParity ∧ b % 2 = r.secondParity ∧
        (a = 0 → r.firstZeroAllowed = true) ∧
        (b = 0 → r.secondZeroAllowed = true)) →
        a = r.firstDesired ∧ b = r.secondDesired := by
    simpa only [decide_eq_true_eq] using hpair
  exact hforced ⟨hsum, hfirst, hsecond, hzeroFirst, hzeroSecond⟩

#print axioms row_count
#print axioms all_allocations
#print axioms forced_allocation

end AllocationFacts228
'''
    destination = H / "lean" / "AllocationFacts228.lean"
    receipt = H / "data" / "allocation-facts-source.json"
    if destination.exists() or receipt.exists():
        raise FileExistsError("Preserve the existing source and preparation receipt.")
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(source.encode("utf-8"))
    result = dict(
        status="PREPARED_UNCHECKED",
        source=str(destination), source_sha256=sha(destination),
        generator=str(Path(__file__).resolve()), generator_sha256=sha(Path(__file__)),
        input_pins=pins, width=raw["width"], row_count=len(rows), rows=rows,
        expected_axiom_reports=["AllocationFacts228.row_count", "AllocationFacts228.all_allocations", "AllocationFacts228.forced_allocation"],
        scope="Literal finite allocation arithmetic only. Extraction of flags from allowed domains is native. Actual-path parity, zero-crossing face capacity, domain-preprocessing preservation and enumeration coverage remain separate. Lean has not been invoked.",
    )
    receipt.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], "rows": len(rows), "source_sha256": result["source_sha256"], "receipt_sha256": sha(receipt)}))


if __name__ == "__main__":
    main()
