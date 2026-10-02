# JSP-000896 / Erdős 1078

Lean formalization of the exact minimum-degree threshold for a transversal clique in a balanced multipartite graph.

For every `r ≥ 2` and `n ≥ 1`, put

$$
 s=\lfloor r/2\rfloor,\qquad
 D=\left\lceil\frac{sn}{2s-1}\right\rceil,\qquad
 T=(r-1)n-D.
$$

The final finite result proves both:

- Every simple `r`-partite graph on `Fin r × Fin n`, with no within-part edges and every vertex degree strictly above `T`, has a transversal clique.
- An actual graph on that same vertex type exists with every vertex degree at least `T` and no transversal clique.

The independent-transversal formulation has sufficiency at maximum degree strictly below `D` and an actual sharpness graph at maximum degree at most `D`. Both fixed-`r` normalized threshold limits and the large-`r` coefficient limit `1/2` are included. The finite theorem has the full original range, including `r = 2`, `r = 3`, `r = 5`, `n = 1`, and every ceiling residue.

## Proof and entry points

- [`MATHEMATICAL_SOLUTION.md`](MATHEMATICAL_SOLUTION.md): the complete finite proof, sharpness construction, exact rounding, and original limits, with primary references.
- [`SOURCE_MAP.md`](SOURCE_MAP.md): the source corresponding to each mathematical step.
- [`JSP896/Main.lean`](JSP896/Main.lean): the final assembly.
- [`JSP896/Statement.lean`](JSP896/Statement.lean): the literal graph, degree, transversal, and threshold definitions.
- [`verification/FullAxiomAudit.lean`](verification/FullAxiomAudit.lean): transitive axiom-check entry point.

The principal declarations are

```lean
JSP896.independentTransversal_of_degree_lt_threshold
JSP896.transversalClique_of_degree_gt_threshold
JSP896.exists_independent_sharpness_at_threshold
JSP896.exists_sharpness_at_threshold
JSP896.full_resolution
JSP896.full_resolution_with_original_limits
```

The sufficiency chain constructs its finite domination certificates, matching configurations, unique-neighbor cells, residual auxiliary graphs, expanded-cell partition, centroid, and both independent-set switches. The sharpness chain defines actual finite graphs by component, side, and position labels, and proves the two forcing chains by induction.

## Pinned environment and reproduction

- Lean: `leanprover/lean4:v4.35.0-rc3`
- Mathlib: `2a885768dae569d938bb9ff3474da6a8753bb90a`
- All transitive dependency revisions: [`lake-manifest.json`](lake-manifest.json)

With Elan installed, run from the project root:

```text
elan toolchain install leanprover/lean4:v4.35.0-rc3
elan run leanprover/lean4:v4.35.0-rc3 lake exe cache get
elan run leanprover/lean4:v4.35.0-rc3 lake build JSP896
elan run leanprover/lean4:v4.35.0-rc3 lake env lean verification/FullAxiomAudit.lean
elan run leanprover/lean4:v4.35.0-rc3 lake env leanchecker --verbose JSP896.Main
```

The cache step obtains the official Mathlib compilation cache for the pinned revision. The subsequent commands compile the local proof source, report the final theorem dependencies, and replay the final module. Actual run records and source hashes are kept with the verification evidence. Compiler binaries and dependency checkouts are installed through the fixed environment and are not part of the source tree.

## Mathematical sources and attribution

The original problem is due to Bollobás, Erdős, and Szemerédi. The exact even threshold and the explicit sharpness construction are described by Szabó and Tardos; Haxell and Szabó determine the odd threshold. This submission's contribution is the Lean formalization, its complete original-scope assembly, and its reproducible verification materials. See [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md) and the references in the mathematical solution.

## Executed verification

The complete pinned build, all 21 actual axiom reports, and final-module kernel replay passed. The publication run completed 24 processes with natural exit code 0 and unchanged proof-input hashes. See [VERIFICATION.md](VERIFICATION.md), [VerifyOriginalStatement.lean](VerifyOriginalStatement.lean), and the complete [raw execution records](verification/publication_reproduction/).

Formalization, compiler repairs, integration and verification: **peilinliu66-dev**, with ChatGPT/Codex assistance. Mathematical sources are credited separately above and in the source map.
