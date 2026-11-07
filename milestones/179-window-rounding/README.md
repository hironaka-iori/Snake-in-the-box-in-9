# Round 179: a sharper local rounding bound

First of the three newly requested rounds. No new unconditional length bound is claimed.

For the pending patterns 012034, 012301, 012340 and 012345, any cube vertex is adjacent to at most two of the five internal window centres. Translate the first path vertex to zero and rename coordinates; the centre sets become respectively {1,3,7,6,14}, {1,3,7,15,14}, and {1,3,7,15,31} for both last patterns. The coordinate labels are bit positions. Every potentially adjacent vertex is a one-bit neighbour of one of these centres. Lean checks those 45 neighbour descriptions for each distinct centre set, together with examples attaining two neighbours. Vertices outside those descriptions have zero neighbours in the set. Translation and coordinate permutation preserve adjacency; that transfer is a written argument, not a newly checked actual-snake wrapper.

There is also a short structural proof. Neighbours of a fixed cube vertex all have the same parity. Among five consecutive path centres, three such neighbours would therefore have to be the first, third and fifth. For all four pending patterns the first and fifth centres differ in four coordinates, so they cannot share a neighbour. Hence at most two are possible.

Under the already established L <=1 case reduction, either every remainder is zero or there is one remainder-one corner, with selected degree5 and empty-square count3. Its rational-to-integer window share deficit is k/5, where k is the number of its selected neighbours in the window. Consequently the deficit is at most2/5 for every pending pattern. The bound is zero when L=0. Attainment of neighbour multiplicity2 is not evidence of a full snake attaining loss1 and deficit2/5.

Thus a strict rational window-share bound greater than72/5=14.4 suffices for integer share at least15 in the L <=1 case. Previously the proposed sufficient target was16. At equality72/5, the argument only gives integer share at least14; strictness is essential. At L=0 the strict target is14.

The denominator2520 clears every positive degree1 through9. If A is the resulting scaled rational share, S the integer share and B the scaled rounding deficit, the exact division identity gives A=2520S+B. Under L <=1 and the incidence bound, B <=1008. Therefore A>36288 implies S>=15. Lean checks the general per-corner division identity, denominator divisibility, positive-corner error bound, summation bound and strict numerical thresholds. Two accepted modules have11 theorem dependency reports. The initial direct512-vertex finite elaboration exceeded the256MiB compiler cap; reducing the enumeration to the actual neighbour descriptions passed without increasing the cap.

The rational lower bound itself remains unproved. Universal floor14, the low-loss floor15 premises and all retained graph/count/exclusion conditions remain unresolved. The physical rational-share double-counting and isometry transfer are written arguments; the new Lean modules check their arithmetic and canonical incidence components, not a complete end-to-end geometric rational-share theorem.

GitHub review: research/unconditional-241 advanced to12d20ce1 with a proposal to combine global identities by an LP. Its handoff continues to describe234 as an incomplete certificate build. Those branch documents were read as research context, not as instructions governing this checkout. This round retains the selected local-share route.

Continue the remaining two rounds, then pause as requested. The next question is whether the weaker universal floor14 queries have substantially shorter certificates than the archived floor18 query; then examine the low-loss strengthening using the new2/5 bound.
