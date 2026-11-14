# A six-neighbour proof for retained coordinates 0, 1 and 2

**Theorem.** No induced 192-edge path in the nine-cube agrees with entry 87's one-chord candidate in the three low bits at every position.

Write each vertex as its three fixed bits and its six free bits. A change in the fixed bits leaves the free word constant. This divides the candidate into 88 chronological intervals, numbered 0 through 87. The free words of successive intervals are neighbours. Translate the first free word to zero, so even intervals use even words and odd intervals use odd words.

Two local tests certify that same-parity intervals have different free words. First, a pair of retained vertices at distance at most one forbids equality. The intervals are separated by at least one intervening interval. Second, suppose a chronological neighbour of one interval has the same retained vertex as the other interval at two nonconsecutive path positions. Equal free words on the original two intervals would give a forbidden cube edge at those positions. Both tests read directly from the 193 indexed vertices.

The following 32 odd intervals pass these tests pairwise, so their free words exhaust the odd half of the six-cube:

```
1 3 5 7 13 15 17 21 25 27 29 31 37 39 41 45
47 49 51 55 59 61 63 65 67 71 75 79 81 83 85 87
```

Consider the following 33 even intervals:

```
2 6 8 12 14 18 20 22 24 30 32 36 38 42 46 48 52
54 56 58 60 62 64 66 68 72 74 76 78 80 82 84 86
```

The local tests distinguish 523 of their 528 pairs. The odd family distinguishes the other five.

* Interval 23 passes an inequality test against every odd anchor except 25. Since the anchors represent every odd word, intervals 23 and 25 have the same word. Interval 22 is adjacent to 23. Interval 20 cannot be adjacent to 25 because the retained traces coincide at nonconsecutive positions. Thus 20 and 22 differ.
* If two even intervals have the same word, that word has six different odd neighbours. Each neighbour must appear in the list of odd anchors. Four exceptional pairs have too few anchors compatible with both ends:

| Even intervals | Odd anchors which could neighbour both |
|---|---|
| 24 and 56 | 17, 25, 41, 55 |
| 24 and 76 | 17, 25, 41, 75 |
| 48 and 56 | 17, 41, 47, 49, 55 |
| 48 and 76 | 17, 41, 47, 49, 75 |

Thus all 33 even words must be distinct. The six-cube contains only 32 even words. This proves the claim. The four small lists use just the rule forbidding odd neighbours when equal retained vertices occur at nonconsecutive positions.

[Direct reproducer](elementary_012.py) checks every local assertion against the bank, including all 496 odd pairs. Its proof uses neither a Boolean solver nor a maximum-clique algorithm. The lists were discovered by matching feasible distances to the 32 word slots of a parity class.
