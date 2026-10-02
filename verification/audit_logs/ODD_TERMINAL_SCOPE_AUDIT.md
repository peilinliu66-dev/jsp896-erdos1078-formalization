# JSP896 odd-threshold, paired-cell, and terminal-switch source audit

Status: **SOURCE_REVIEWED_ONLY; LEAN_ELABORATION_AND_KERNEL_CHECK_PENDING**. Mathematical review judgment: no fatal error or missing range identified in the reviewed route.

This independent review read the supplied mathematical notes and the literal local proof bodies. It did not run Lean or alter any candidate source. The accompanying JSON binds this review to source hashes. A later source change must be checked against this review. Successful source review is not a substitute for the separately requested actual build and transitive-axiom audit.

No fatal mathematical error or omitted odd parameter range was found in the reviewed route. In particular, the route is uniform for **every odd r=2t+1 with t>=2 and every n>0**, under the exact strict bound `(2t-1)d < t*n`. It does not assume an expanded-cell partition, a switch, or a terminal dominator certificate at the final theorem boundary. At this snapshot the only reviewed Lean file differing from the immutable original is `PairedDeficit.lean`, with one additional Mathlib ring-big-operator import; its mathematical proof body is unchanged.

## Scope and lower-chain boundary

The host is the actual finite graph on `Fin (2*t+1) × Fin n`, with actual first-coordinate classes and the stated degree bound. `Main.independentTransversal_of_odd_bound` works by contradiction, then constructs an edge-minimal spanning no-transversal graph H. Partiteness and the degree bound pass from G to H. It concludes by contradicting H's no-transversal property; it does not transfer an independent set of a subgraph to a supergraph.

The lower certificate chain constructs a full-class faithful induced matching configuration M and places each critical edge in a matching configuration. The full certificate-construction proof is another audit assignment. This review checks the exact inputs consumed by the paired and component route, and checks that Main obtains those inputs from local proved theorems rather than exposing them as hypotheses of the final exported statement. Its lower boundaries are `FeasiblePair.exists_matching_configuration` and `CriticalEdge.every_edge_in_matching`.

The matching interface is literal: induced perfect matching on I, partiteness, connected acyclic class graph, and faithful class edges. Faithfulness prevents parallel class edges. `MatchingFacts.full_card` consequently proves `|I|=2r-2`, not merely an upper bound on the size of some arbitrary certificate. `MatchingFacts.dominates` is proved by orienting the matching tree away from the class of an undominated vertex and appending that vertex.

## Uniform scalar margins and paired deficit

Write m=|I|=2r-2, and let C_i be the vertices whose only neighbor in I is endpoint i. These cells are pairwise disjoint, nonempty because partner(i) belongs to C_i, and have sizes a_i<=d. Put δ_i=d-a_i>=0.

Every vertex has at least one neighbor in I under the no-transversal hypothesis. Vertices outside the cell union have at least two such neighbors. Counting incidences therefore gives

`sum_i a_i >= 2*r*n - m*d`.

For r>=5 the original structural bound `(2r-4)d < (r-1)n` implies

`(4r-5)d < 2*r*n`.

Indeed, multiplying the first strict inequality by 2r and comparing the coefficients after multiplication of the desired inequality by r-1 leaves

`2r(2r-4) - (r-1)(4r-5) = r-5 >= 0`.

The implication is thus valid at r=5 as well as above it. The incidence lower bound gives

`sum_i δ_i = m*d - sum_i a_i <= 2*m*d - 2*r*n < d`.

This is the strict total deficit used by all subsequent deletions. It is not supplied as an independent host-graph assumption in Main.

For the residual-cell graph, auxiliary edges omit within-cell and opposite-cell edges. Opposite-cell completeness gives a vertex in C_i at least a_partner(i) original neighbors, so its auxiliary degree is at most δ_partner(i). A feasible dominating certificate on selected index set S, s=|S|>=2, has multiplicity

`t_i <= s-1 - 1_{partner(i) in S}`.

`CertificateMultiplicity` proves this bound by mapping every nonisolated certificate vertex in cell i to the class of one certificate neighbor. Faithful class edges make this map injective. Same-cell and opposite-cell adjacency exclusions remove exactly the two indicated forbidden classes. This is stronger than merely knowing a total certificate cardinality, and the source actually proves the stronger bound.

After deletions R_i with total at most d, domination implies

`s*d - sum_{i in S}δ_i - sum_{i in S}|R_i| <= sum_{i in S} t_i*δ_partner(i)`.

Reindexing by the involution makes the coefficient of δ_j on the two right-hand deficit terms equal to

`1_{j in S} + 1_{partner(j) in S}*t_partner(j) <= s-1`.

It follows that `(s-1)d <= (s-1)sum_i δ_i < (s-1)d`, a contradiction. `PairedCellTransversal.hasFull_of_paired_deficit` obtains its certificate from the lower proved existence theorem; the certificate is not an input hypothesis.

## Literal residual choices and simultaneous expanded-cell completion

`CellDeletion.representatives_after_deletion` uses the actual dependent finite type of residual cell vertices. Its label fibers have precisely the residual cell cardinalities. The auxiliary-to-original degree budget is proved by a disjoint neighbor union, with no estimate added as an unsupported premise. Its output f satisfies `G.Adj (f i) (f j) iff partner(i)=j`.

`MatchingExchange.exchange_all` turns those representatives into a matching configuration. It replaces one coordinate at a time. Every mixed selection consisting of target representatives and old partner endpoints still has exactly the original involution as its adjacency relation. The next target representative is consequently in the correct unique-neighbor cell of the current matching, so the proved single-edge exchange applies. The class tree is constructed at every step; an arbitrary matching with unproved class connectivity is not substituted.

To show every vertex v is complete to some old cell, assume each cell contains a nonneighbor of v and delete its neighbors from all cells. At most d vertices are deleted and all residual cells remain nonempty. The residual representatives give a genuine new matching configuration avoiding v, contradicting its domination property. Two distinct cells have combined size greater than d because their combined deficits are below d, so v cannot be complete to two cells.

For expanded opposite cells, take a complete to C_partner(i) and b complete to C_i. The proof deletes simultaneously

`U=(N(a) minus C_partner(i)) union (N(b) minus C_i)`

from every old cell. Its size is at most δ_i+δ_partner(i)<d. For the distinguished C_i, only the first term of U can delete vertices, and δ_partner(i)<|C_i|. For C_partner(i) the symmetric estimate applies. For a third cell C_j, `δ_j+δ_i+δ_partner(i)<d` gives `|C_j|>δ_i+δ_partner(i)>=|U|`. Thus every residual cell stays nonempty.

The new matching configuration has a adjacent to exactly its chosen partner(i) representative and b adjacent to exactly its chosen i representative. Those representatives are partners. The earlier proved opposite-cell completeness, applied to the new configuration, therefore forces a adjacent to b. No estimate on a changed intermediate unique-neighbor cell is used. This verifies the simultaneous asymmetric deletion argument at r=5, avoiding the larger-r numerical estimate from the paper's separate structure argument.

Define B.index(v) as the partner of the unique cell to which v is complete. This gives an actual partition and the old matching index identity. Opposite expanded fibers are complete. Every fiber has size at most d, and the partition of all rn vertices gives a lower bound

`|fiber_i| >= rn - (m-1)d`.

Every matching configuration J dominates the graph. At most `E=m*d-rn` vertices can have at least two J-neighbors. The same scalar margin gives `rn-(m-1)d > E`. If two J vertices shared one expanded fiber, every vertex of its opposite fiber would have at least two J-neighbors, contradicting that budget. Thus J has exactly one vertex in every expanded fiber. Its induced matching edges must join opposite fibers. Critical-edge containment then proves that the **entire** edge-minimal graph has exactly the opposite-fiber adjacency relation. `CellStructure.to_bipartiteModel` derives both model fields from this argument; no extra-edge exclusion is assumed.

## Constructed centroid and orientation

`MatchingOrientationCentroid.exists_centroid` minimizes the actual total tree distance over the finite set of classes. Across an edge root-child, distances from each reachable vertex differ by exactly one, by unique paths in a forest. The source sums that identity to obtain

`score(child)+2*|branch(root,child)| = score(root)+r`.

Minimality and r=2t+1 imply each branch has at most t classes. Neither centroid existence nor branch size is an external premise.

For every nonroot class c the source chooses a literal matching endpoint black(c) in c whose partner is closer to the root. Two chosen black endpoints cannot be adjacent: partner adjacency would force the distance of each class to be smaller than that of the other. Their colors give injectivity; their partners are also injective and disjoint from the blacks. Their total number is 2(r-1)=|I|, so they cover every distinguished matching endpoint. The unused root value is never counted.

Parent arcs point away from the root, with each endpoint distance increasing by exactly one. Induction on decreasing distance constructs root-to-class parent reachability. Triangle inequalities then show that every nonroot parent descendant lies in the corresponding first centroid branch. Therefore each nonroot parent-descendant set has at most t classes. This bound is proved from the metric centroid and the constructed orientation, rather than added to `RootOrientation`.

## Two switches and finite dominator terminal block

The auxiliary arc x->y means y is nonroot and an actual vertex in class x has distinguished neighbor black(y). Every parent arc is witnessed by white(y), so the root reaches all classes.

For S containing the root, the switch set uses all vertices with distinguished black neighbor in S, and retains black endpoints in classes outside S. Exact model adjacency proves this set independent. If every class in S has an arc back into S, the witnesses cover S and retained blacks cover its complement. Selecting one vertex per class from this independent covering set gives an actual full transversal.

For any auxiliary edge x->y with a route y->x, choose S to be all classes reaching x. The root is in S. Every z!=x has its first step toward x in S; x uses the edge to y. This closed switch applies even to a self-loop. Hence, under no full transversal, auxiliary reachability is antisymmetric, and a directed cycle cannot be used silently.

If a vertex v has distinguished neighbor white(c) and a root-to-class(v) route avoids c, choose S to be all classes reaching class(v) along a route avoiding c. Then the root is in S, c is outside S, and every member except the terminal class has a step inside S. The vertex v lies on the opposite side of component c to the used white-type vertices, and component c has no white-type vertex in the switch set. Therefore inserting v preserves independence and covers the terminal class. This is the proved avoiding-path switch. Under the no-transversal hypothesis it shows c dominates class(v).

The finite digraph facts have full proof bodies. A nonroot c dominates x when no root-to-x route avoids c. Dominators of a fixed x are comparable; otherwise concatenating an avoiding prefix with an appropriate suffix contradicts domination, using antisymmetric reachability to exclude the obstructing reverse route. A root dominator of x is selected by maximizing the number of reachable future vertices among its nonroot dominators. A strict predecessor has a larger future set, so this choice has no distinct nonroot dominator. Comparability proves uniqueness.

Next choose a root dominator c minimizing its future cardinality and set L={x:c dominates x}. Then c belongs to L and the root does not. Two closures are proved:

1. If x belongs to L and x->y, y belongs to L. Otherwise choose the root dominator e of y. If e!=y, append x->y to any root-to-x route: since y!=e, e must already dominate x. Uniqueness forces e=c, a contradiction. If e=y, the route c->x->e makes e a distinct root dominator with a strictly smaller future set, contradicting minimality.
2. If x belongs to L and a nonroot d dominates x, d belongs to L. Comparability gives c dominates d or d dominates c. The latter and root-domination force d=c.

Every parent route is an auxiliary route, so c occurs on the root-to-x parent route for x in L. Thus L is contained in c's parent-descendant set and `1<=|L|<=t`.

Every vertex in a class of L has a distinguished neighbor black(d) or white(d). The first closure puts d in L for a black neighbor; the avoiding-path switch and the second closure do the same for a white neighbor. Its distinguished neighbor cannot be black(c), because that would give class(v)->c together with c->class(v), triggering the cycle switch. Consequently

`D=({black(d):d in L} union {white(d):d in L}) minus {black(c)}`

is an actual dominating set for all vertices of the classes in L, with `|D|<=2|L|-1`. Deleting black(c) really decreases cardinality because it is present in the union. The source proves domination using `B.uniqueNeighbour`, not a numerical proxy for actual adjacency.

For s=|L|<=t, the original strict bound yields `(2s-1)d<sn`: the needed comparison is `t(2s-1)<=s(2t-1)`, equivalent to s<=t. Actual domination and degree counting yield `sn<=|D|d<=(2s-1)d`, contradiction. This completes all odd r>=5, all positive n, without asymptotic or divisibility restrictions.

## External reference and finite challenges

The live primary source [Haxell–Szabó, Odd independent transversals are odd](https://page.mi.fu-berlin.de/szabo/PDF/oddtransversal.pdf), Theorem 4.1 on printed page 14, confirms the all-odd component conclusion. The source's r>=7 structural restriction belongs to an earlier theorem, not to Theorem 4.1. This candidate separately proves the stronger uniform r>=5 structure route above. No Jin theorem or paper theorem is used as an axiom.

An independent finite challenge script enumerated 33,866 topologically ordered DAGs on 2..6 vertices, including 10,105 with the root reaching every vertex. Direct enumeration of all root-to-vertex paths checked existence and uniqueness of root dominators and both terminal-block closures for 14,909 minimum-rank blocks, with no counterexample. It also checked 2,364 maximum-multiplicity paired-coefficient cases for 1..4 pairs, with no counterexample. The script and results are saved next to this report. These checks only challenge finite instances of the combinatorial lemmas; the universal reasoning is the source review above, and actual Lean verification remains separate.

## Required final acceptance

The builder must still complete elaboration, full project construction, final expanded-statement inspection, and the actual transitive-axiom audit on frozen final inputs. The reviewed odd route has no mathematical obstruction identified. Any repair that changes quantifiers, graph definitions, strict threshold, certificate faithfulness, or the literal constructions must be returned for mathematical review.
