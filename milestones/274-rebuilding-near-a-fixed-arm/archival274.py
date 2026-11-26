"""Recover earlier rooted partner ceilings by explicit eight-dimensional vertex sequences."""
from hashlib import sha256

def archival_bound_rows(load, digests, sources, take, normalize):
    def add(round_no, ordered, cap, evidence):
        vertices, word, axes = normalize(ordered)
        root = sha256(vertices).hexdigest()
        evidence = dict(evidence, reference_start=ordered[0], reference_axes=axes)
        take(round_no, root, list(vertices), cap, evidence)
        return root

    donor_file = "248-rooted-arm-capacity/parents.json"
    audit_file = "249-long-parent-joins/audit.json"
    donors = {row["donor_index"]:row["path"] for row in load(donor_file)["rows"]}
    audit = load(audit_file)
    assert audit["inputs"]["milestones/" + donor_file] == digests[donor_file]
    sources[249] = dict(parents=donor_file, bounds=audit_file)
    for i, row in enumerate(audit["cases"]):
        end = row["endpoint"]
        assert end in (0,1)
        p = donors[row["donor"]][::1 if end == 0 else -1]
        assert row["edges"] == len(p)-1 and row["excluded_at_192"] == (len(p)+row["upper"]<192)
        add(249,p,len(p)+row["upper"],dict(file=audit_file,row=["cases",i],donor=row["donor"],
                endpoint=end,partner_ceiling=row["upper"]))

    census_file = "252-shorter-reference-segments/census-68.json"
    bounds_file = "252-shorter-reference-segments/replay-68-192.json"
    paths_file = "253-repeated-segment-growth/closure.json"
    census = load(census_file)
    proof = load(bounds_file)
    paths = load(paths_file)["paths"]
    assert proof["census_sha256"] == digests[census_file] and proof["target"] == 192
    assert proof["all_excluded"] and proof["all_new_endpoints_reviewed"]
    new_ids = {r["id"] for r in proof["endpoints"]}
    assert all({r["end"] for r in proof["endpoints"] if r["id"]==s and r["status"]=="excluded"}=={0,1}
               for s in new_ids)
    assert new_ids <= set(census["all_ids"]) and len(census["all_ids"])-len(new_ids)==proof["archived_classes"]
    sources[252] = dict(census=census_file,bounds=bounds_file,representatives=paths_file)
    for shape in census["all_ids"]:
        p = paths[shape]
        assert sha256(min(normalize(p)[1],normalize(p[::-1])[1])).hexdigest()==shape
        for end,q in enumerate((p,p[::-1])):
            add(252,q,191,dict(file=bounds_file,census=census_file,shape_id=shape,endpoint=end))

    archive_file = "269-archived-93-arms/archive.json"
    archive = load(archive_file)
    for filename, expected in archive["sources"].items():
        if filename not in digests:
            load(filename)
        assert digests[filename] == expected
    sources[269]["complete_archive"] = archive_file
    named = {}
    complete = set()
    for name,row in archive["examples"].items():
        cube=row["vertices"]; j=row["crossing_index"]; axis=row["axis"]
        assert cube[j]^cube[j+1]==1<<axis
        assert sum((u^v)==1<<axis for u,v in zip(cube,cube[1:]))==1
        for side,part in enumerate((cube[:j+1][::-1],cube[j+1:])):
            p=[]
            for v in part:
                y=v^part[0]
                p.append((y&((1<<axis)-1))|((y>>(axis+1))<<axis))
            sh=sha256(min(normalize(p)[1],normalize(p[::-1])[1])).hexdigest()
            for which,q in (("at_crossing",p),("opposite_end",p[::-1])):
                record=row["arms"][side][which]
                root=sha256(normalize(q)[0]).hexdigest()
                assert record["shape"]==sh and record["root"]==root and record["edges"]==len(q)-1
                assert record["upper"]<192
                complete.add(root)
                value=record["upper"]
                if root not in named or named[root][0]>value:
                    named[root]=(value,q,dict(file=archive_file,row=["examples",name,"arms",side,which],
                                               original_round=record["source_round"],archive_axis=axis,crossing_index=j))
    assert len(complete)==sum(row["excluded"] for row in archive["unique_roots"].values())==294
    for root,(upper,p,evidence) in named.items():
        assert add(269,p,upper,evidence)==root



def rooted_prefix_reasons(literal, prior, normalize, isometry):
    """Deleting the free-end suffix of the fixed arm preserves every opposite arm."""
    normalized = normalize(literal)[0]
    reasons = []
    for size in range(1,len(literal)):
        matches = prior.get(normalized[:size], ())
        if not matches:
            continue
        extra = len(literal)-size
        strongest = min(row[3] for row in matches)
        for round_no, key, path, upper, receipt in matches:
            if upper != strongest:
                continue
            reasons.append(dict(kind="rooted_prefix",round=round_no,source_root=key,
                 first_index=0,last_index=size-1,added_edges=extra,source_ceiling=upper,
                 ceiling=upper+extra,receipt=receipt,mapping=isometry(literal[:size],path)))
    return reasons

