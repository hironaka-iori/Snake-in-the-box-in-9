# Radius4 adaptive score: minimal scales, stronger cheap scores, and an exact positive encoding

Research continuation of29October2026. This file contains proved scalar and double-counting lemmas, explicit small induced-path witnesses, and finite checks. It does not prove a new numerical bound on a(9), does not claim a completed window survey, and does not modify the original repository.

## 1. Set-up and the three-vertex restriction

Let S be a subset of Q9 containing no complete coordinate square; every induced snake has this property. Let x be selected. For an empty2face F at graph distance one from x, there is a unique containing3cube R_x(F) that contains x. Write t_x(F)=|S intersect R_x(F)|, and h(F)=the number of nonempty3cubes containing F. The adaptive score is

    a(x)=alpha(x)+sum_{F empty,dist(x,F)=1} 2/(h(F)*t_x(F)).

Since F is empty, all selected vertices of any nonempty mother3cube lie on its opposite2face. That opposite face cannot have all four vertices selected. Thus

    1<=t_x(F)<=3,   1<=h(F)<=7.

No endpoint, global connectedness, or maximum-degree premise is needed for this restriction; absence of a full coordinate square suffices.

The uniform score is

    g(x)=alpha(x)+sum_F 2/(7*t_x(F)).

Therefore21g(x) is integral: each individual coefficient becomes6/t, in{6,3,2}. Similarly1260a(x) is integral: its coefficient becomes2520/(h*t), integral for every h in1..7,t in1..3.

## 2. The scales21 and1260 are genuinely minimal for the FULL pointwise scores

It is not enough to show a least common multiple of isolated coefficients: complete pointwise sums might cancel denominators. Explicit genuine snakes rule out that possibility.

First induced path (14vertices), with root x=18 at index7:

    [4,5,13,9,8,10,26,18,19,17,49,33,32,34].

Exact calculation gives

    alpha(18)=20,  a(18)=36421/180,  g(18)=1156/21.

Second induced path (27vertices), with root x=10 at index5:

    [4,5,7,15,11,10,8,24,16,17,19,51,35,34,32,96,64,65,67,
     195,131,130,128,384,256,257,259].

Here

    alpha(10)=19, a(10)=42611/315, g(10)=347/7.

Both roots are internal. Every unordered pair was checked for adjacency iff consecutive. Fractions are reduced. Any universal integer scale for a must therefore be divisible by both180 and315, whose lcm is1260. Any universal scale for g must be divisible by21. Together with the sufficient scales above, this proves both minima, even when only internal vertices of genuine snakes are considered.

## 3. All21(h,t) combinations are attainable; no coefficientwise improvement

Fix F={0,1,2,3}, free coordinates0,1. Choose h distinct outer coordinates2,...,h+1. In each unit outer layer e_i+Q2, place an induced Q2path with prescribed size t_i in{1,2,3}. Start it at the previous layer's outgoing Q2vertex, and use distinct heavy-coordinate flips0,1 to reach its outgoing endpoint. Between consecutive unit layers i,i+1 insert the single connector at outer word e_i+e_(i+1), with the common heavy endpoint.

The outer sequence

    e2, e2+e3, e3, e3+e4, e4, ...

is induced. Nonconsecutive outer layers are nonadjacent; adjacent unit/connector layers have exactly the intended shared heavy endpoint. Within each unit layer the chosen Q2path is induced. Therefore the entire construction is an induced path. It has sum_i t_i+(h-1) vertices. Its h nonempty mother3cubes of F have precisely the occupancies t_i. Connectors have two outer bits and belong to no mother3cube of F.

Hence every h in1..7 and t in1..3 occurs in an actual snake. The weak per-term bound2/(ht)>=2/21 is sharp, attained at h=7,t=3 in the27vertex example. Sharpening the coefficient solely by forbidding some(h,t) pair cannot work; improvements need simultaneous information from multiple empty faces or their neighboring empty cubes.

## 4. A stronger cheap score using only empty2faces and empty3cubes

Let e2(x)=#empty2faces at distance one from x, and e3(x)=#empty3cubes at distance one from x. Define

    D(x)=sum_{empty F,dist(x,F)=1} (7-h(F)).

Then

    D(x)=3*e3(x).

Proof: D counts pairs(F,R), where F is an empty2face at distance one from x and R is an empty mother3cube. Such an R cannot contain selected x, but contains a vertex at distance one from x, so dist(x,R)=1. A coordinate cube at distance one from x has a unique nearest vertex y. Exactly three of its six2faces contain y, and these are exactly its faces at distance one from x. This counts every empty R exactly three times.

For every integer h in1..7,

    2/(3h)>=(13-h)/63,

because their difference is(h-6)(h-7)/(63h)>=0. Since t<=3,

    2/(ht)>=(13-h)/63.

Sum over F and use D=3e3:

    a(x)>=alpha(x)+(6e2(x)+D(x))/63
         =alpha(x)+(2e2(x)+e3(x))/21.

Thus the old cheap share alpha+2e2/21 has the additional unconditional positive term e3/21. The new score uses only positive Boolean emptiness indicators and scale21; it does not require the exact1260scale reciprocal objective.

## 5. Discrete support family: six inequalities, four nonnegative PB objectives

For every integer r in1..6 and h in1..7,

    2/(3h)>=2(2r+1-h)/(3r(r+1)),

since the difference equals2(h-r)(h-r-1)/(3h*r*(r+1))>=0. Summing as above gives the general proved inequality

    a(x)>=alpha(x)+[4(r-3)/(3r(r+1))]*e2(x)
                        +[2/(r(r+1))]*e3(x).

For r3..6 all coefficients are nonnegative and the PB scales are small:

| r | lower score | integer PB score |
|---|---|---|
|3|alpha+e3/6|6alpha+e3|
|4|alpha+e2/15+e3/10|30alpha+2e2+3e3|
|5|alpha+4e2/45+e3/15|45alpha+4e2+3e3|
|6|alpha+2e2/21+e3/21|21alpha+2e2+e3|

The pointwise maximum of these four scores is also a valid lower bound on a. No choice of a single r dominates all others. In the relaxed problem that retains only e2,e3 and t<=3, the full six-line family is the lower convex envelope for sum1/h with prescribed mean h=7-3e3/e2. This last optimality statement concerns that numerical moment relaxation; it does not claim attainability of all simultaneous geometric moment assignments by snakes.

## 6. A directly certifiable cheap encoding

Fix a selected window centre x. There are36coordinate squares through x,252coordinate2faces at distance one from x, and504coordinate3cubes at distance one from x. All their vertices lie in B(x,4).

For an empty-cube indicator z_C, encode its equivalence to all corner variables being false with

    (-z_C OR -s_v), for every vertex v in C;
    (z_C OR s_v1 OR ... OR s_vk).

The same definition handles empty faces and the three other corners of singleton squares at selected x. The r6 objective is precisely the integer weighted cardinality expression

    21*sum(singleton indicators)+2*sum(empty2face indicators)
                                      +sum(empty3cube indicators).

A hypothesized upper threshold becomes a positive weighted PB constraint. The other three objectives use the table above. Without sharing indicators between centres, their basic equivalence definitions require792indicator variables and5940clauses per centre, before PB auxiliaries and existing path-degree constraints. Shared corner sets should be deduplicated across centres. These are explicit encoding specifications, not claims that a new SAT/Lean implementation has already been completed.

## 7. Exact1260scale objective without21way one-hot products

For one empty F put H_r=[h(F)<=r], B=[t_x(F)<=2], C=[t_x(F)=1]. The exact coefficient satisfies

    2520/(ht)=120+60B+180C
         +sum_{r=1}^6 H_r*(A_r+B_r*B+C_r*C),

where

    A=[420,140,70,42,28,20],
    Bcoeff=[210,70,35,21,14,10],
    Ccoeff=[630,210,105,63,42,30].

All coefficients are positive integers. Proof:1/h=1/7+sum_r [h<=r]/(r(r+1)), while1/t=(2+[t<=2]+3[t=1])/6. Multiplying these exact identities gives the displayed formula. Gate all terms with F's emptiness indicator. The required atoms are emptiness, cardinality thresholds h<=r, thresholds t<=2/t=1, and conjunctions of those Booleans. This supplies a positive threshold/AND encoding with no need to multiply integer h and t or enumerate21exact pairs. It is not asserted to be smaller than every optimized one-hot encoding; it offers a monotone alternative compatible with totalizers and existing weighted-threshold machinery.

## 8. Reproduction and status

Run local_coefficients.py and coefficient_identities.py in this directory with standard Python. The former verifies23small induced paths, all21(h,t) examples,259selected-root score evaluations, the minimum-scale witnesses, D=3e3 by an independent empty3cube enumeration, and all six inequalities at every tested root. The latter checks all126scalar(h,t,r) inequalities and all21exact positive threshold identities using exact fractions.

These finite checks supplement the proofs above. They are not a window survey or a universal numerical upper-bound proof. No Lean compilation or large solver computation was run. All witnesses and exact values are in local_coefficients.json; scalar coefficient data are in coefficient_identities.json.

## 9. A direct global inequality for incidence LPs

Write B2=sum_{x in S}e2(x), B3=sum_{x in S}e3(x), s0=#empty squares, and U0=#undominated empty squares. The new r6bound has the following direct global form for EVERY set S containing no complete coordinate square:

    2B2+B3<=42(s0-U0).

For an empty F let K(F)=#selected vertices at distance one from F. Its seven opposite-face fibres are disjoint, so K=sum_j t_j<=3h. Double counting gives B2=sum_F K and3B3=sum_F(7-h)K, the latter being the global sum of D(x)=3e3(x). Thus

    2B2+B3=sum_F(13-h)K/3
           <=sum_{F:h>0}h(13-h)
           <=42*#dominated empty squares,

because h(13-h)<=42 for integer h1..7. Terms with h=0 have K=0. This proves the inequality without referring to the adaptive score or any window model.

For a nontrivial Q9snake, combine with T+2s0=9214-35v to obtain

    21T+2B2+B3<=21(9214-35v).

This supplies a valid extra incidence relation for a global LP/discharging treatment. By itself it is not a numerical improvement: no adequate new universal lower bound on B2/B3 or their window means has yet been established.

## 10. Singleton/two-point3cube bonuses: strictly stronger cheap objectives

Define C1(x) as the number of coordinate3cubes containing selected x whose selected intersection is exactly{x}. Define C2,d(x), d=1,2,3, as the number of3cubes containing x whose selected intersection has exactly two vertices, at Hamming distance d. These definitions include the distance3case explicitly.

For each adjacent empty F retain t=t_x(F). Let E_le2(x) count these F with t<=2, and E1(x) count those with t=1. Then

    E1=3C1,
    E_le2=3C1+2C2,1+C2,2.

Proof. A mother3cube with exactly one selected point x has three empty square faces; all three are opposite x. For exactly two selected vertices at distance d, precisely3-dcoordinates are constant across both vertices. For each such coordinate its opposite square face is empty, giving3-dempty faces. Thus distance1 contributes2, distance2 contributes1, and DISTANCE3CONTRIBUTESZERO. Any adjacent empty F whose mother through x has t<=2 arises exactly in one of these cases. The above identities follow by counting these pairs(F,mother).

Set

    V(x)=E_le2(x)+3E1(x)=12C1(x)+2C2,1(x)+C2,2(x).

The exact identity1/t=(2+[t<=2]+3[t=1])/6 and the h-support inequality give, for r in3..6,

    a(x)>=alpha(x)+4(r-3)e2(x)/(3r(r+1))+2e3(x)/(r(r+1))
                       +2(r-3)V(x)/(3r(r+1)).

Proof: for each F,

    2/(ht) >= (2+[t<=2]+3[t=1])*(2r+1-h)/(3r(r+1)).

Split off the leading2term, which sums to the old support-family score in section5. In the remaining term,2r+1-h>=2r-6>=0. Substituting this minimum gives the additional coefficient2(r-3)/(3r(r+1)) times E_le2+3E1. This proves the displayed inequality. No assumption about endpoint distance or joint extension of the local model is used.

The four nonnegative integer objectives are now:

| r | stronger integer score, divided by the stated scale |
|---|---|
|3|6alpha+e3, scale6|
|4|30alpha+2e2+3e3+V, scale30|
|5|45alpha+4e2+3e3+2V, scale45|
|6|21alpha+2e2+e3+V, scale21|

All extra Cstatistics are radius3statistics. The e3term still sets the overall required radius at four. They fit the project's share/w3window direction while retaining positive, small integer coefficients. It has not yet been shown that any associated window mean crosses a new numerical upper-bound threshold.

## 11. Stronger direct global incidence lemma including low-occupancy3cubes

Let N1 count all coordinate3cubes with exactly one selected vertex. Let N2,d count all coordinate3cubes with exactly two selected vertices at distance d. Summing V over selected x gives

    sum_x V(x)=12N1+4N2,1+2N2,2.

A one-selected cube contributes once to C1. A two-selected cube contributes once at each of its two roots, hence the factors two. There is NO N2,3term because its empty-face contribution is zero.

The stronger r6pointwise inequality and the exact adaptive accounting imply the general global lemma

    2B2+B3+12N1+4N2,1+2N2,2 <=42(s0-U0).

It also has the following direct proof without adaptive scores. For every empty F let n_t(F) count its nonempty mother fibres with occupancy t, t=1,2,3. Put h=n1+n2+n3 and K=n1+2n2+3n3. The contribution of F to the left side is

    (13-h)K/3+4n1+2n2
      =h(13-h)+2(h-7)n1/3+(h-7)n2/3
      <=h(13-h)<=42       if h>0.

For h=0 its contribution is zero. The term(13-h)K/3 is the B2/B3contribution proved in section9. Counting singleton/two-point mother cubes against their empty faces gives the remaining4n1+2n2term, equivalently sum_xV. Summing over dominated empty F proves the lemma.

Consequently every nontrivial Q9snake satisfies the NEWproved global incidence inequality

    21T+2B2+B3+12N1+4N2,1+2N2,2 <=21(9214-35v).

This is a new valid relation for the research pipeline, not a numerical theorem improving its current upper bound. The natural next computational task is an exact small-window threshold survey of one of the four strengthened positive objectives, followed by certificates and a soundness bridge.

## Additional verification for sections10–11

local_coefficients.py now verifies the new r6occupancy bonus at all259selected roots of23genuine small paths, including the exact identities for E1/E_le2. bonus_validation.py separately checks every one of120integer fibre-occupancy distributions with h<=7 against the direct global inequality, all84scalar(h,t,r) strengthened inequalities with r3..6, and all singleton/two-point3cube patterns rooted at0. In particular the opposite-point pattern{0,7} has zero empty square faces. Results are in bonus_validation.json. These checks supplement the general proofs above and do not replace a future window-mean proof.
