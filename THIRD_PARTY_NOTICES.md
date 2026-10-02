# Sources and dependency notices

## Mathematical attribution

The original balanced multipartite threshold problem is from B. Bollobás, P. Erdős, and E. Szemerédi, *On complete subgraphs of r-chromatic graphs*, Discrete Mathematics 13 (1975), 97–107. [Original paper](https://users.renyi.hu/~p_erdos/1975-19.pdf).

T. Szabó and G. Tardos, *Extremal problems for transversals in graphs with bounded degree*, Combinatorica 26 (2006), 333–351, gives the exact even-part threshold and Construction 3.3 used for the literal all-size sharpness graph. [Author manuscript](https://www.renyi.hu/~tardos/tibortransversal.pdf).

P. Haxell and T. Szabó, *Odd independent transversals are odd*, Combinatorics, Probability and Computing 15 (2006), 193–211, proves the exact odd-part threshold. Its feasible-pair, induced-matching, and cell framework underlies the local sufficiency proof; the odd-component proof implements its two switching mechanisms through finite reachability and terminal dominators. [Author manuscript](https://page.mi.fu-berlin.de/szabo/PDF/oddtransversal.pdf).

The local `JSP896` files implement these mathematical arguments, the uniform paired-deficit structure route for `r ≥ 5`, the original finite and asymptotic assembly, and the associated verification interfaces in Lean. The mathematical solution and the source map give the derivation and corresponding declarations.

## Formalization source

The starting local project was supplied in `FULL_SOURCE_JSP896_UNCOMPILED_20261001T1943.zip`, SHA-256

```text
ab1edb1ae5928d16e407c52cf1b38d28e9c46044493f6659b9bc2cdfa2e743e3
```

The original archive is preserved by the audit workflow. The public source records the resulting local formalization and any compiler/API repairs, together with the fixed toolchain and verification evidence.

## Lean and Mathlib

The proof uses [Lean 4](https://github.com/leanprover/lean4) and [Mathlib](https://github.com/leanprover-community/mathlib4). Mathlib is pinned at `2a885768dae569d938bb9ff3474da6a8753bb90a`; all dependency revisions and repository URLs are recorded in `lake-manifest.json`. These dependencies are fetched by Lake rather than vendored into the submitted source tree.

Their source retains the respective upstream license and copyright notices in each fetched dependency checkout. Mathlib uses the Apache License 2.0; Lean's upstream distribution includes its own license and third-party notices. Reproduction uses the pinned upstream repositories and official cache.
