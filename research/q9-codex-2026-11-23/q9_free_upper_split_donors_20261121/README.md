# Free second layer over punctured Q8 donors

The input catalogue contains 753 words. This run uses all 726 length-96 donors and all 26 length-97 donors. Each gives one pair of deleted internal vertices. The pair is separated by at least 12 steps along the donor and has cube distance two or three. Each length-97 donor also gives one single-hole placement. The fixed lower layer is exactly the retained vertex set. The upper layer has no prescribed donor.

For a dual-hole placement the constructive beam orders and orients the three lower pieces, embeds a short upper connector through legal cube vertices, and grows a second upper connector. A single-hole placement uses one upper connector between the two lower pieces. Width 18 was used on all 778 placements. The top 64 by first-pass length were rerun at width 160. The heuristic limits the short connector, samples orders, and truncates the beam. Its 842 output paths are checked individually in check.py.

The unrestricted SAT search permits any upper path components that result in one connected Q9 snake and uses a budget of 800 conflicts per placement. Five independent two-crossing 191-edge reference placements serve as positive controls, with upper polarities set to their known witnesses. They also have independent lower-target positive controls using empty upper hints.

For six placements, including the two with the longest constructions, separate integer duals in dual16 bound the total vertex count for each of the two endpoint colours of a 192-edge path. The comparison threshold is 1930000 at scale 10000. The Python checker independently reconstructs each dual value. These certificates apply to the stated exact lower-layer placements and the 192-edge target. The full cube is unrestricted above that layer apart from columns ruled out by lower degree two.

Run `python3 -B q9_free_upper_split_donors_20261121/check.py` from the repository root to validate catalogue reconstruction, output paths and integer duals. The beam can be rebuilt with C++17. The SAT experiment uses python-sat MiniCard, and the dual generator uses the existing SciPy factor code. The output in summary.json is the result of the independent checks.
