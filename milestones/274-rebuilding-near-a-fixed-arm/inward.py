"""Extract the explicit change of crossing that turns the selected 188 into an archived 189."""
from near import HERE,MS,read,write,valid,shape
def main():
    src=read(HERE/"selected-start.json")["rebuilt97"]
    rows=read(HERE/"rebuilt97-placements.json")["roots"]
    plan=read(HERE/"face274/rebuilt97/plan.json")["roots"]
    seed=src["seed"];old=src["reference"];pairs_before=valid(old,9)
    old_arm=len(seed)-1
    qk=next(k for k,r in rows.items() if r["best"]["edges"]==189 and plan[k]["minimum_omissions"]==1)
    changed=rows[qk]["literal_join"];pairs_after=valid(changed,9)
    kept=changed[:old_arm][::-1]
    partner=[v-256 for v in changed[old_arm:]]
    assert kept==seed[1:] and kept[0]==partner[0]==seed[1] and set(kept)&set(partner)=={seed[1]}
    assert len(src["other"])==91 and len(partner)==93 and len(old)==189 and len(changed)==190
    previous=read(MS/"271-rebuilt-historical-partners/long-joins.json")["witnesses"]
    matches=[r["parent_key"] for r in previous if r["canonical_transition_word"]==shape(changed)]
    assert len(matches)==1
    write(HERE/"crossing-one-step-inward.json",dict(original_join=old,original_arm=seed,original_partner=src["other"],
        rebuilt_join=changed,rebuilt_arm=kept,rebuilt_partner=partner,
        old_crossing=[seed[0],256+seed[0]],new_crossing=[seed[1],256+seed[1]],removed_from_original_arm=[seed[0]],
        split_before=[97,1,90],split_after=[96,1,92],original_pairs=pairs_before,rebuilt_pairs=pairs_after,
        round_271_shape_match=matches[0],exact_fixed_maximum_before=188,exact_fixed_maximum_after=189))
    print("Crossing",seed[0],seed[1],"gives 188 to 189 with all pairs checked.")
if __name__=="__main__":main()
