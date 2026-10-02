# Verified pinned project

On 2 October 2026, the 45 local library/root modules compiled. The publication-directory reproduction passed 3221 Lake jobs, all 24 recorded processes exited naturally with code 0, and all active source hashes remained unchanged. All nine dependency checkouts matched their fixed revisions and had clean source workspaces. The supplied Lean and dependency versions were retained.

The six expanded-target, nine main proof-chain, and six initial-chain reports contain only dependencies from `propext`, `Classical.choice`, and `Quot.sound`. The expanded entry spells out the literal finite graph conclusions, all quantifiers and neighbor counts, both fixed-r limits, and the original BES expression `c_r - (r - 2) → 1/2`. Actual outputs are in [publication_reproduction](verification/publication_reproduction/); [publication-summary.json](verification/publication-summary.json) records every reported dependency.

Official `leanchecker --verbose JSP896.Main` returned naturally with code 0 and emitted the actual `replaying JSP896.Main` marker. The replay uses the pinned imported environment. Separate transitive axiom reports cover the final theorem and the combinatorial proof chain.

## Reproduce

With Python 3.10+ and Elan, install the exact toolchain and run:

```text
elan toolchain install leanprover/lean4:v4.35.0-rc3
python verify_project.py --cache
```

The optional `--cache` retrieves the official complete pinned Mathlib cache. A new checkout then builds its project sources. The recorded publication run reused the exact pinned dependency and candidate project caches; `lake --rehash` checked source inputs and rebuilt the changed publication documentation copies. Compiler binaries, dependency checkouts, and binary build outputs are external to the source tree.

Exact proof commands:

```text
elan run leanprover/lean4:v4.35.0-rc3 lake --rehash build JSP896
elan run leanprover/lean4:v4.35.0-rc3 lake env lean VerifyOriginalStatement.lean
elan run leanprover/lean4:v4.35.0-rc3 lake env lean verification/FullAxiomAudit.lean
elan run leanprover/lean4:v4.35.0-rc3 lake env lean verification/InitialAxiomAudit.lean
elan run leanprover/lean4:v4.35.0-rc3 lake env leanchecker --verbose JSP896.Main
```

## Source correspondence and repair evidence

[accepted-proof-inputs.json](verification/accepted-proof-inputs.json) binds all 51 Lean/build/lock inputs to the actual checked bytes. The exact finite graph definitions and version pins match the supplied archive. Compiler fixes changed 27 original Lean files (+198/-122 lines); repair logs and source snapshots are preserved under [audit_logs](verification/audit_logs/). The literal original-statement audit is a separate proved entry.

The public copy updates 14 historical source-status comments to point to these records; executable proof code is preserved and the complete public copy was reverified. Mathematical solution and source correspondence are supplied in [MATHEMATICAL_SOLUTION.md](MATHEMATICAL_SOLUTION.md) and [SOURCE_MAP.md](SOURCE_MAP.md).
