# Round 258 · The first exchange that leaves the six reference shapes

Four simultaneous replacements in the smaller parity class of a 96-edge arm can produce a seventh shape. The first such move is possible only from reference 0 among the six reference shapes. Every set reached in at most three replacements had already been classified in [Round 257](../257-three-exchange-parents/README.md).

| Reference | Sets passing the neighbour count | Sets admitting an arm | Labelled arms, up to reversal |
|---|---:|---:|---:|
| 0 | 2,164 | 2 | 2 |
| 3 | 2,182 | 2 | 2 |
| 4 | 3,949 | 2 | 7 |
| 5 | 2,182 | 2 | 2 |
| 8 | 2,182 | 2 | 2 |
| Sixth reference | 4,048 | 2 | 2 |
| Total | 16,707 | 12 | 17 |

A 96-edge path in the eight-dimensional cube visits 48 sites of one parity and 49 of the other. For each reference there are \(\binom{48}{4}\binom{80}{4}=307{,}743{,}836{,}400\) candidate smaller classes at distance four. The counts in the table are per reference, so their combined domain has 1,846,463,018,400 reference–candidate pairs. Each passing set was completed in two ways. One algorithm enumerated spanning orders of the 48 sites and all possible intervening labels. The other contracted forced edges and enumerated cycles through an auxiliary vertex representing the two endpoints. Their lists of labelled paths agreed for every passing set. [Enumeration](enumerate.py) · [Reference 0 and its two completions](shell-0.json)

The first class producing the new shape removes vertices \(42,115,164,179\) and inserts \(38,176,227,242\). A second class removes \(70,88,115,117\) and inserts \(16,82,100,227\). The resulting paths agree up to translation, permutation of the coordinates and reversal. Their shape lies outside the 264-shape catalogue used at the start of this round. [Ordered vertices of the new arm](new-arms.json)

At both ends of the new arm, a certificate excludes an unrestricted 95-edge partner. A longer partner would contain such a prefix. The arm also has no one-edge extension at either end in its own face. Consequently, in a one-crossing snake of at least 192 edges, the smaller class of any 96-edge segment in either face can meet the smaller class of any of the six references in **at most 43 sites**, under every cube isometry. Indeed, overlap of at least 44 would place the segment in a classified shell of radius at most four. If it were a proper segment of the arm, a neighbouring edge would extend it. If it were the whole arm, the opposite arm would require at least \(192-96-1=95\) edges. The earlier certificates and endpoint checks apply to the original six shapes. [Both new certificate replays](partner-replay-95.json) · [Earlier endpoint argument](../255-parity-exchange-arms/README.md)

For a positive construction we placed every directed segment of 114 donor shapes at each endpoint. The longest compatible donor segments had 54 and 40 edges. At each end we removed the last eight edges of one longest placement and enumerated every legal continuation of the retained prefix. Two searches agreed on 77 and 70 partner edges, respectively. The resulting joins have 174 and 167 edges. These maxima are relative to their retained prefixes. [Both explicit joined paths, comparison counts and donor exclusions](constructed.json)

To replay the supply counts independently, consider adding a new site \(a\). Choose two of its eight possible path neighbours. After deleting the proposed old sites, at most one old neighbour of each chosen site can remain, since its final degree is at most two and \(a\) is another neighbour. Enumerating these deletion requirements gives a set of possible insertions for each deleted quadruple. A retained site with exactly two usable labels must keep both. If a required label already has two neighbours, no new site adjacent to it can be inserted. The replay finally computes degrees in the completed set and compares the ordered list of surviving exchanges with the first enumeration. [Independent supply calculation](replay_supply.py)
