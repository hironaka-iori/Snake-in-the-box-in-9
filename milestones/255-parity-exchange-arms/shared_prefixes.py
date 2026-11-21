"""Use replayed first-step exclusions on a sibling when its freed sites are avoided."""
from pathlib import Path
import partners255 as driver

HERE = Path(__file__).resolve().parent


def main():
    original_sources = driver.sources
    original_model = driver.shared.anchored_model
    data_file = HERE / "partner-caps.json"
    replay_file = HERE / "partner-replay-95.json"
    data = driver.read(data_file)
    replay = driver.read(replay_file)
    driver.require(replay["ledger_sha256"] == driver.file_hash(data_file), "Stale prefix replay")
    verified = {(r["shape"],r["end"]):r for r in replay["roots"]}
    cuts = []
    def sources():
        old, pins = original_sources()
        for item in data["roots"].values():
            key = item["shape"], item["end"]
            status = verified[key]
            rows = driver.shared.query_rows(item,95)
            parent = item["parent"]
            driver.require(status["root"] == item["root"] and status["prefixes"] == len(rows),
                           "Incomplete source replay")
            if status["status"] == "excluded":
                driver.require(driver.shared.covers((0,),rows,parent,95),"No rooted covering proof")
                old["255/" + key[0],key[1]] = (parent,94)
            for prefix, row in rows.items():
                if len(prefix)>1 and row["status"] in {"excluded","inherited"}:
                    cuts.append((set(parent[1:]),prefix[1:]))
        pins.update({p.name:driver.file_hash(p) for p in (data_file,replay_file,Path(__file__))})
        return old,pins
    def anchored(prefix):
        base = original_model(prefix)
        def model(parent,length,rules):
            if length != 95:
                raise ValueError("Source exclusions apply at length 95")
            cnf, chosen = base(parent,length,rules)
            forbidden = set(parent[1:])
            extra = set()
            for before, steps in cuts:
                freed = before - forbidden
                if len(freed) <= 6 and not (forbidden & set(steps) or freed & set(steps)):
                    extra.add(tuple([-chosen[v] for v in steps] + [chosen[v] for v in sorted(freed)]))
            cnf.clauses.extend(map(list,sorted(extra)))
            return cnf,chosen
        return model
    output = HERE / "shared-proofs"
    output.mkdir(exist_ok=True)
    driver.HERE = output
    driver.LEDGER = output / "cases.json"
    driver.sources = sources
    driver.shared.anchored_model = anchored
    driver.main()


if __name__ == "__main__":
    main()
