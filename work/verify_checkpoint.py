"""Read-only validation of supplied witnesses and the published Q9 subset."""
import json
from pathlib import Path
from check_snake import verify

root = Path(__file__).resolve().parents[1]
for name, dimension in [("snake9_witness.json",9),("short_maximal_witness.json",9),
                        ("snake8_witness.json",8),("square_counterexample.json",9)]:
    data = json.loads((root/"outputs"/name).read_text())
    actions = data["transition_sequence"]
    result = verify(actions,dimension)
    original = data["vertex_sequence"]
    assert [v ^ original[0] for v in original] == result["vertex_sequence"], name
    print(f"{name}: {len(actions)} edges, all pairs checked")
bank = json.loads((root/"work/bank9.json").read_text())
assert len(bank) == 131
for data in bank:
    checked = verify(data["transition_sequence"])
    assert checked["edges"] == 191
    assert checked["vertex_sequence"] == data["vertex_sequence"]
print("All 131 bank entries checked; no optimality inference.")
