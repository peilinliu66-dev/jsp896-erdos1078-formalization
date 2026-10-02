# JSP896 finite certificate and cell-structure source audit

Status: **SOURCE_REVIEWED; COMPILATION_PENDING**. This reviewer performed no Lean invocation, changed no candidate source and made no publication. The conclusions below are an independent review of the literal definitions and proof bodies. The attachment's own statements that it had been reviewed were not used as evidence of correctness.

The source review found no fatal mathematical gap in the route from a counterexample graph to a complete bipartite model. This is a source-level conclusion, not a claim that the proofs elaborate or have been accepted by Lean. The snapshot JSON records the source bytes at report save; compiler repairs made afterwards need to be compared with it. At save time, 24 of the 26 reviewed source files matched the original ZIP bytes. The two changed files were also reviewed by exact diff: `FiniteTransversal` changed substitution/elaboration syntax and supplied an explicit reflexive inequality, and `PairedDeficit` added the big-operator ring import. These edits introduce no mathematical hypothesis. Line ranges below otherwise refer to the unchanged original source; declaration positions are recorded in the snapshot for comparison.

## Hypotheses closed in the final assembly

`Main.lean:29–69` starts with the actual balanced graph on `Fin (2*t+1) × Fin n`, with `t ≥ 2`, `n > 0`, partiteness, maximum degree at most `d`, and `(2*t-1)*d < t*n`. Assuming no full transversal, it constructs an edge-minimal subgraph `H` that still has no transversal. Partiteness and the maximum-degree bound transfer from the original graph to `H`; the part sizes are unchanged. The argument proves a contradiction for `H`; it does not transfer an independent transversal of a subgraph to the original graph.

The structural threshold `(2*r-4)*d < (r-1)*n` at `r = 2*t+1` is exactly twice the odd threshold, so it is a consequence of the input bound, without an additional assumption. The `r ≥ 5` condition follows from `t ≥ 2`. The cases `r = 2,3` and even `r` are handled separately in `Main.lean:72–107`; the structural result is not silently applied outside its range.

`BipartiteModel M` is a literal structure with an index into the matching endpoints, exact unique adjacency to the matching, and exact adjacency between arbitrary host vertices (`MatchingTree.lean:70–75`). Its existence is proved in `CellStructure.lean:159–177`, and `Main.lean:60–64` supplies the apparently extra `hcritical` input from `CriticalEdge.every_edge_in_matching` on the same edge-minimal graph. Neither this structure nor an IMC/certificate existence premise survives as a hypothesis of the final theorem.

## Actual finite maximality and feasible growth

`FiniteTransversal.lean:14–25` defines partial and full transversals using actual host adjacency, injectivity of the class labels, and equality of the label image with all classes. `exists_maximum` (`45–56`) maximizes the cardinality over a finite powerset. Missing-class domination (`86–100`), the strict cardinality bound without a full transversal (`102–116`), and same-colour swaps (`118–161`) are proved from these definitions; these particular ranges use the compiler-edited snapshot.

`FeasiblePair.lean:53–67` retains all ten concrete invariants, including saturation, unique center for every leaf, class acyclicity/connectedness, faithful ordered class edges, and local star minimality. In particular, the simple class graph alone does not encode exclusion of parallel class edges: the independent `faithful` invariant is essential, and is actually maintained.

For an undominated vertex in an active or missing class, `FeasibleGrowth.lean:46–113` proves the existence of a leaf. In the active-class case it swaps out the unique existing same-colour representative; all other stars remain fixed, while the star at that representative's center loses one leaf. This contradicts local minimality. In the missing-class case it contradicts maximality directly. There is no augmenting-path or termination oracle.

`CompatibleStars.lean` proves the old/new star separation and that new leaves have inactive labels. `FaithfulExtension.lean:38–82` proves faithfulness for all combinations of old and new edges; two new leaf endpoints with the same label agree because they lie in the partial transversal. `ClassTreeGrowth.lean:29–111` constructs the new class tree by adding genuinely fresh leaf classes. `FeasibleExtension.lean:11–134` then proves every feasible invariant, including local minimality for both old and new centers, and `136–155` proves a strict increase of the actual vertex set cardinality.

`DominationCertificate.lean:33–83` chooses a feasible extension with maximal actual set cardinality from a finite set of pairs `(I,T)`. Any active-class undominated vertex would produce a strictly larger feasible extension. Nonemptiness is proved by selecting a vertex in a missing class if `I` were empty. `ExtendsSeed` preserves the initial endpoints and the initial representatives in active seed classes. This closes certificate existence on the actual graph, not on a prescribed abstract interface.

## Full induced matching and critical edges

`CertificateSize.lean:12–71` uses actual ordered class darts: faithful class edges inject every nonisolated certificate vertex into a class dart, and class acyclicity bounds the number of class edges by `q-1`. Thus `|I| ≤ 2(q-1)` for `q` active classes. Actual domination counts give `q*n ≤ |I|*d`. If `q ≤ r-1`, the strict structural threshold gives a contradiction (`CertificateIMC.lean:15–23,54–86`). Therefore all classes are active.

`CertificateMatching.lean:16–68` splits the certificate into centers and leaves. Each center has a distinct leaf. If their cardinalities agree, surjectivity proves that the induced certificate graph is a perfect matching. Otherwise the independent partial transversal contains the leaves and has fewer than `r` vertices, giving `|I| ≤ 2*r-3`. The structural threshold implies `(2*r-3)*d < r*n` (`CertificateIMC.lean:25–33`), so domination excludes the second alternative. `toMatchingTree` supplies all six literal matching-tree fields.

`CriticalEdge.lean:60–77` constructs an actual edge-minimal counterexample by finite minimization of the number of ordered adjacency pairs. Removing any actual edge then yields a full transversal. Such a transversal contains both removed endpoints (`88–109`). From it `exists_critical_seed` (`113–263`) builds the one-edge feasible seed, including faithful class edges and local minimality: a center with an unavailable label must have at least one neighbour in every eligible maximum partial transversal, so its star cannot have fewer than two vertices. The dominating extension retains both seed endpoints; the degree counting above makes it a full IMC (`267–289`). Therefore `every_edge_in_matching` (`292–305`) is derived for every actual edge of the edge-minimal graph.

`MatchingFacts.lean:14–64` proves, from a literal matching tree, that its cardinality is `2*r-2` and it dominates every vertex if no full transversal exists. The latter uses the explicit distance-decreasing root-oriented partial transversal constructed in `MatchingOrientation.lean:48–110`; an undominated vertex in its missing class would complete it.

## Cells, cut support and exact replacements

`MatchingCells.lean:21–56` defines a cell by the condition that a vertex has exactly the specified matching endpoint as its neighbour among all matching vertices. Thus the cells are disjoint actual subsets, and opposite matching endpoints belong to the expected cells. The cell is indexed by its matching neighbour, not by its class label.

The two-root completion at `MatchingCells.lean:61–157` explicitly picks a distance-decreasing matching endpoint in each nonroot class. Two selected endpoints cannot be adjacent because they would each have smaller distance than the other. Two undominated nonadjacent root vertices then complete an actual full transversal.

After deleting a matched pair, `strip_classGraph` (`193–242`) proves equality with deletion of the single corresponding class edge. This equality uses faithfulness and the unique partner property; it is not inferred merely from the simple class graph. The deleted edge is a bridge, every class reaches one of its endpoints, and `cell_across_cut` (`281–307`) uses the two-root completion to force every unique-neighbour cell onto the opposite side of the cut. `opposite_cells_complete` (`310–338`) then proves actual complete adjacency of the paired cells by contradiction with a full transversal.

`MatchingExchange.lean:13–148` constructs a replacement IMC by deleting the old matched pair and inserting opposite-cell representatives. It proves matchedness, class acyclicity/connectedness, and faithfulness separately. Cut separation excludes an old class edge parallel to the inserted edge. `exchange_all` (`153–284`) replaces one coordinate at a time. Intermediate choices contain the other old or new representative of the matched pair, and their induced adjacency remains precisely the prescribed partner relation; the final matching tree is therefore constructed rather than assumed.

## Paired deficit theorem and residual graph

`CertificateMultiplicity.lean:31–96` injects each certificate fibre into allowed neighbouring labels using nonisolation and faithful class edges. Its cardinality is at most `s-2` if the partner label lies in the active set, and `s-1` otherwise. This is the exact multiplicity inequality needed by the deficit proof; a total bound `2*s-2` is not substituted for it.

`PairedDeficit.lean:60–121` proves the weighted inequality by reindexing under the involution. For each label the combined coefficient is at most `s-1`, giving

`sum_selected δ + sum_selected t_i*δ_partner(i) ≤ (s-1)*sum_all δ < (s-1)*d`.

With total removal at most `d`, the lower fibre-size bound requires at least `s*d - sum_selected δ - removal` vertices, which contradicts this upper domination budget. `PairedCellTransversal.lean:20–81` constructs the actual feasible dominating certificate when assuming the auxiliary graph has no full transversal, derives its multiplicity bounds, and uses this contradiction. It exports only graph and numerical hypotheses.

`CellDeletion.lean:14–133` builds the literal residual sigma type consisting of `(cell index, remaining vertex)`, whose value map is injective because the cells are disjoint. The auxiliary graph consists of original host edges between different, nonpartner cells. The residual fibres are nonempty; their sizes are actual differences of finset cardinalities. Neighbours in the auxiliary graph and the full original opposite cell are disjoint host neighbours, hence the auxiliary degree is at most the deficit of that opposite cell. All inputs to the paired deficit theorem are proved, including surjectivity, excluded within/partner edges, degree, size and removal budgets. Its actual choices induce exactly the prescribed paired matching in the host graph; `imc_after_deletion` (`139–155`) proves they form a new full IMC via simultaneous exchange.

## Uniform scalar budget and expanded partition

For `r ≥ 5`, `StructureBounds.lean:8–20` derives `(4*r-5)*d < 2*r*n` from `(2*r-4)*d < (r-1)*n` and `d ≥ 0`. Indeed

`2*r*(2*r-4) - (r-1)*(4*r-5) = r-5 ≥ 0`.

This argument includes the exact boundary `r=5`; no strict loss is taken there. `CellCounting.lean:83–210` counts actual incidences and proves `core_mass ≥ 2*r*n - (2*r-2)*d`. Therefore

`sum_i(d-|C_i|) ≤ (4*r-4)*d - 2*r*n < d`.

The actual cell-cardinality degree bound makes every deficit nonnegative. `ExpandedCells.lean:21–69` shows every vertex is complete to some unique original cell by deleting all its cell neighbours: otherwise every residual cell is nonempty, and the replacement IMC would not dominate that vertex. Uniqueness follows because any two complete cells have combined mass exceeding `d`.

`expanded_opposite_complete` (`71–228`) deletes the extra neighbours of two prospective opposite expanded vertices simultaneously. The deletions have total size at most `δ_i+δ_partner(i) < d`. The proof checks nonemptiness separately for both distinguished cells and every third cell, using the corresponding pair or triple deficit bound. The residual representatives give a new literal IMC in which the two vertices belong to opposite unique-neighbour cells, hence they are adjacent. `exists_expanded_partition` (`237–260`) constructs the index and all its fields. The index convention is consistent: a vertex in original cell `C_i` has expanded index `i`, while matching endpoint `i` has expanded index `partner(i)`.

## Removal of extra edges and audit conclusion

For every expanded fibre, `CellStructure.lean:31–66` bounds its size above by `d` and below by `r*n-(2*r-3)*d`. For any other full IMC, the number of vertices dominated by at least two of its endpoints is at most `(2*r-2)*d-r*n` (`CellCounting.lean:141–163`). The scalar budget makes the lower fibre bound strictly greater than this exceptional budget. Thus two endpoints of another IMC cannot share an expanded index (`CellStructure.lean:68–105`). Since both IMCs have exactly `2*r-2` vertices, every expanded fibre is represented exactly once. Unique matched neighbours then force every edge inside such an IMC to join opposite expanded fibres (`107–129`). Critical-edge containment puts every actual host edge in one such IMC, completing exact adjacency for the whole graph (`133–153`).

No mathematical fatal defect, weakened final hypothesis, circular reliance on the structure theorem, assumed replacement configuration, or unproved certificate-existence premise was identified in the reviewed source route. No specific Lean API/elaboration defect is asserted here because this reviewer did not invoke Lean. A successful complete build plus actual axiom reports and final theorem statement expansion remain necessary to upgrade this source review to a verified result.
