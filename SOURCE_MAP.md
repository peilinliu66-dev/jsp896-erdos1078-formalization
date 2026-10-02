# Source map for JSP-000896 / Erdős 1078

`JSP896.lean` imports the final `JSP896.Main` module. The proof tree has 44 modules in `JSP896/`, plus that root import file. Every mathematical stage below is implemented by local proof bodies. Dependencies on Mathlib are fixed by `lake-manifest.json`.

## Original statement and final exports

| File | Mathematical content and principal declarations |
| --- | --- |
| [`JSP896/Statement.lean`](JSP896/Statement.lean) | Literal vertices `Fin r × Fin n`, actual neighbor-count degree, `IsPartite`, both transversal predicates, cross-part complement, integer thresholds, and `FullResolution`. |
| [`JSP896/Complement.lean`](JSP896/Complement.lean) | The actual complement degree sum `(r-1)*n` and the strict/non-strict degree adapters. |
| [`JSP896/Main.lean`](JSP896/Main.lean) | Original-scope sufficiency for every `r ≥ 2`, `n > 0`; `independentTransversal_of_degree_lt_threshold`, `transversalClique_of_degree_gt_threshold`, `full_resolution`, and `full_resolution_with_original_limits`. |
| [`JSP896.lean`](JSP896.lean) | Public root import of the final theorem. |

## Finite domination certificate and prescribed-edge IMCs

| File | Obligation discharged |
| --- | --- |
| [`JSP896/FiniteTransversal.lean`](JSP896/FiniteTransversal.lean) | Literal partial/full independent transversals, existence of a cardinality maximum, insertion and same-class swaps. |
| [`JSP896/FeasiblePair.lean`](JSP896/FeasiblePair.lean) | All feasible-pair invariants, including faithful class edges and local star minimality; compatible transversals and finite minimal choices. |
| [`JSP896/FeasibleGrowth.lean`](JSP896/FeasibleGrowth.lean) | The local swap contradiction ensuring an undominated new center has a genuine leaf. |
| [`JSP896/CompatibleStars.lean`](JSP896/CompatibleStars.lean) | Preservation of old stars, agreement on active classes, inactivity of new leaf classes, and disjointness of new/old stars. |
| [`JSP896/ClassTreeGrowth.lean`](JSP896/ClassTreeGrowth.lean) | Acyclicity and connectedness when an actual star of new class leaves is attached. |
| [`JSP896/FaithfulExtension.lean`](JSP896/FaithfulExtension.lean) | Exact class-graph formula, faithful edge preservation, and the new class tree. |
| [`JSP896/FeasibleExtension.lean`](JSP896/FeasibleExtension.lean) | Proof of every invariant for the attached star; a compatible extension with strictly larger first set. |
| [`JSP896/DominationCertificate.lean`](JSP896/DominationCertificate.lean) | Finite maximal extension yields a nonempty certificate dominating its active classes; seed vertices and seed-class representatives persist. |
| [`JSP896/CertificateSize.lean`](JSP896/CertificateSize.lean) | `|I| ≤ 2|S|-2` from the faithful acyclic class graph and nonisolated certificate vertices. |
| [`JSP896/CertificateMultiplicity.lean`](JSP896/CertificateMultiplicity.lean) | Per-cell certificate multiplicity is at most `|S|-1`, or `|S|-2` when the opposite cell is selected and opposite edges are excluded. |
| [`JSP896/FiniteGraphCounting.lean`](JSP896/FiniteGraphCounting.lean) | Actual neighbors, fibers, active-class counts, incidence sums, and domination by the sum of degrees. |
| [`JSP896/CertificateMatching.lean`](JSP896/CertificateMatching.lean) | A feasible star forest is a perfect induced matching or has at most `2r-3` vertices; conversion to a literal matching tree. |
| [`JSP896/CertificateIMC.lean`](JSP896/CertificateIMC.lean) | Under `(2r-4)d < (r-1)n`, certificates use every class and are IMCs; `exists_matching_configuration` constructs one. |
| [`JSP896/CriticalEdge.lean`](JSP896/CriticalEdge.lean) | Finite edge minimization, actual one-edge deletion, a feasible seed from its full transversal, and `every_edge_in_matching`. |

## Matching cells and the uniform structure proof

| File | Obligation discharged |
| --- | --- |
| [`JSP896/MatchingTree.lean`](JSP896/MatchingTree.lean) | Literal perfect induced matching with faithful class tree, partner involution, and exact `BipartiteModel` interface. |
| [`JSP896/MatchingOrientation.lean`](JSP896/MatchingOrientation.lean) | Rooted independent partial transversals selected from matching endpoints and completion by an undominated root-class vertex. |
| [`JSP896/MatchingFacts.lean`](JSP896/MatchingFacts.lean) | Exact `2r-2` IMC cardinality and domination by every full-class IMC in a no-transversal graph. |
| [`JSP896/MatchingCells.lean`](JSP896/MatchingCells.lean) | Literal unique-neighbor cells; deleting a matching edge, its two class-tree cuts, cut support, and complete opposite cells. |
| [`JSP896/MatchingExchange.lean`](JSP896/MatchingExchange.lean) | One-pair exchange with all matching-tree invariants, and actual simultaneous representative exchange by finite induction. |
| [`JSP896/CellCounting.lean`](JSP896/CellCounting.lean) | Unique-cell mass, total deficit, multiply dominated vertex count, and `total_cell_deficit_lt` for all `r ≥ 5`. |
| [`JSP896/StructureBounds.lean`](JSP896/StructureBounds.lean) | Scalar implication `(2r-4)d < (r-1)n ⇒ (4r-5)d < 2rn`, including the strict `r=5` boundary. |
| [`JSP896/PairedDeficit.lean`](JSP896/PairedDeficit.lean) | Involution reindexing and the weighted sum contradiction for every selected opposite-pair membership pattern. |
| [`JSP896/PairedCellTransversal.lean`](JSP896/PairedCellTransversal.lean) | A genuine auxiliary-graph independent-transversal theorem derived from the constructed certificate and its multiplicity bounds. |
| [`JSP896/CellDeletion.lean`](JSP896/CellDeletion.lean) | Actual residual sigma-type graph, residual fiber cardinalities and degree bounds, representatives, and conversion into a replacement IMC. |
| [`JSP896/ExpandedCells.lean`](JSP896/ExpandedCells.lean) | Every vertex completes a unique old cell; simultaneous asymmetric deletion proves opposite expanded completeness; construction of the full expanded partition. |
| [`JSP896/CellStructure.lean`](JSP896/CellStructure.lean) | Every IMC has exactly one representative per expanded cell; critical edges exclude all extra edges; `bipartiteModel_of_edges_in_imcs` constructs the exact disjoint complete-bipartite model. |

## Odd-component switches and terminal domination

| File | Obligation discharged |
| --- | --- |
| [`JSP896/MatchingOrientationCentroid.lean`](JSP896/MatchingOrientationCentroid.lean) | A centroid selected by a finite minimum of total tree distance; exact edge-distance balance and branch cardinality bound. |
| [`JSP896/OddComponentsOrientation.lean`](JSP896/OddComponentsOrientation.lean) | Actual black/white endpoints for a rooted IMC, endpoint coverage, and parent reachability. |
| [`JSP896/OddComponentsReachability.lean`](JSP896/OddComponentsReachability.lean) | Finite routes, routes avoiding a class, dominator comparison, finite future rank, unique root dominators, and both terminal-block closure properties. |
| [`JSP896/OddComponentsSwitching.lean`](JSP896/OddComponentsSwitching.lean) | Auxiliary arcs, explicit independent covering sets, the closed-cycle switch, the avoiding-path switch, acyclic reachability, and white-neighbor domination. |
| [`JSP896/OddComponentsCentroid.lean`](JSP896/OddComponentsCentroid.lean) | Parent distance increments and containment of every nonroot descendant set in an actual centroid branch. |
| [`JSP896/OddComponentsTerminal.lean`](JSP896/OddComponentsTerminal.lean) | Construction of a nonempty terminal class block `L`, the actual dominating set with fewer than `2|L|` endpoints, and the odd-bound contradiction. |
| [`JSP896/OddComponentsCounting.lean`](JSP896/OddComponentsCounting.lean) | Exact cardinality of selected balanced classes and the degree bound excluding domination of `ℓ ≤ t` classes by `2ℓ-1` vertices. |
| [`JSP896/OddComponents.lean`](JSP896/OddComponents.lean) | `hasFull_of_odd_components`, assembling the constructed centroid, orientation, switches, and terminal dominating-set contradiction. |

## Small cases, extremal examples, rounding, and limits

| File | Obligation discharged |
| --- | --- |
| [`JSP896/EvenSufficiency.lean`](JSP896/EvenSufficiency.lean) | Equivalence of set-based and function-based literal transversals; ordinary domination sufficiency, including every smaller active class set. |
| [`JSP896/SmallCases.lean`](JSP896/SmallCases.lean) | Two-part nonneighbor construction and the three-part maximum-forward-degree triangle procedure. |
| [`JSP896/SharpnessTools.lean`](JSP896/SharpnessTools.lean) | Literal component/Boolean-side label graph, degree bound by position injection, finite class reindexing, isolated-class padding, and the `n ≤ d` witness. |
| [`JSP896/SharpnessChains.lean`](JSP896/SharpnessChains.lean) | Explicit two-chain component/side/position functions, injectivity, independent class checks, and forcing of opposite central sides. |
| [`JSP896/Sharpness.lean`](JSP896/Sharpness.lean) | Positive-remainder arithmetic and actual sharpness graphs for all even, odd, and arbitrary numbers of parts. |
| [`JSP896/ThresholdArithmetic.lean`](JSP896/ThresholdArithmetic.lean) | Exact strict ceiling equivalence, positivity and capacity bounds, complement threshold adapters, and both sharpness witnesses at the computed ceiling. |
| [`JSP896/ThresholdAsymptotics.lean`](JSP896/ThresholdAsymptotics.lean) | Ceiling sandwich, fixed-number-of-parts threshold limits, half-part growth, large-part coefficient limit, and assembly with the finite resolution. |

## Verification interfaces

[`verification/FullAxiomAudit.lean`](verification/FullAxiomAudit.lean) checks the principal declarations and requests their transitive axiom dependencies. The build workflow records actual commands, exit codes, pinned dependency revisions, and the source hashes of the compiled project. The final `Main` module can also be replayed with Lean's `leanchecker` in the same pinned environment.

The mathematical argument corresponding to this source map is in [`MATHEMATICAL_SOLUTION.md`](MATHEMATICAL_SOLUTION.md). Its references distinguish the published mathematical theorems from the applicant's Lean formalization.
