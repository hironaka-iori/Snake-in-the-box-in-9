# A five-shape proof of the 33-against-32 obstruction

For the triple of retained bits {0, 1, 4}, the 528 individual contact checks have a short geometric explanation. Interpret each retained word as an integer in {0, 1, 2, 3, 16, 17, 18, 19}. Say two sets *touch* when they contain words at Hamming distance at most one. Use the following five shapes.

| Shape | Even intervals assigned to it |
|---|---:|
| {2} | 8 |
| {3} | 12 |
| {0, 1} | 9 |
| {0, 19} | 1 |
| {1, 18} | 3 |

Assign an even interval to the first shape it contains. Scanning the retained trace gives exactly the counts above. Every pair of shapes touches. For instance, 2 touches 0 and 18; 3 touches 1 and 19. Among the doubletons, the first and second share 0, the first and third share 1, and the second and third contain the adjacent words 0 and 1. The two singletons are adjacent.

Consequently, intervals containing any of these shapes must all have different free words. The five counts sum to 33; only 32 six-bit words of the common parity exist. This proves the exclusion by one scan of the input and a five-by-five check. The argument applies to any family of mutually touching shapes in any retained cube and any free dimension.

**Sharp contact count for these 33 intervals.** The table retains one site in each of 20 intervals and two in each of 13, a total of 46. Every choice of contact witnesses for this same family requires at least 46 sites. Indeed, the family includes traces consisting entirely of {2} and entirely of {3}; at least one site must therefore be retained at 2 and at 3. A one-site witness for any other interval must be within distance one of both. The cube has no triangles, so the only possibilities are 2 and 3 themselves. Exactly 20 of the 33 full traces contain either 2 or 3. Each of the remaining 13 requires at least two sites. This gives the matching lower bound 20+2×13=46, with no integer-programming premise.

[Direct input count](five_shapes.py), [Lean check of the shapes](FiveShapes.lean), and [the original certificate](README.md).

## Transfer to every saved 191-edge snake

Take any one of the 131 bank entries, retain any three coordinate histories, and repeat a projected position anywhere in the order. This specifies 193 indexed base words with six free bits. All 48 isometries of the retained three-cube give 24 distinct images of the five-shape family. On each parity, count the intervals containing any one shape in a given image. A count above 32 excludes the corresponding lift.

This single structural test excludes **7,713 of 2,112,768 indexed choices**, distributed over **all 131 bank entries**. The number per entry ranges from 14 to 299. The strongest example needs 37 words of one parity: entries 128 and 130 both give this count when bits 2, 6 and 7 are retained and the projected vertex at position 92 is repeated. Distinct choices may give identical projected sequences. These are counts of choices, not isometry classes.

To see why the calculation can reuse the original traces, suppose the repeated position belongs to interval r. The intervals before r remain unchanged. Interval r is split into its prefix through that position and its suffix from that position; each part includes the repeated base word once. All later intervals exchange parity. Prefix and suffix counts therefore give the new score exactly. A second implementation rebuilt the full projected sequence and checked every reported exclusion individually. [All positions](bank-shape-exclusions.csv), [direct independent check](verify_bank_shapes.py), [summary](bank-shapes-summary.json) and [enumeration](bank_shapes.cpp).
