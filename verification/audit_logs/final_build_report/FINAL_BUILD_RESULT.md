# Final JSP896 build result: PASSED

Pinned Lean `leanprover/lean4:v4.35.0-rc3` and Mathlib `2a885768dae569d938bb9ff3474da6a8753bb90a`; no version adjustment.

All 45 library modules compiled directly with natural exit 0 and their individual final source hashes bound to the success metadata. Full `lake build JSP896` completed naturally with 3221 jobs. Its complete 47 Lean files plus 3 build pins were byte-identical before and after, and match the present final files.

InitialAxiomAudit: 6 checks; FullAxiomAudit: 9 checks. Both exited naturally with 0, with the same complete final source snapshot before and after. Every reported axiom dependency is within `propext`, `Classical.choice`, and `Quot.sound`; the JSON records each exact observed dependency set.

All 64 original extracted file hashes and the saved ZIP SHA256/CRC were checked. All nine live dependency Git revisions match the original manifest and have clean tracked/untracked worktrees. Pinned dependency repositories and compilation cache were reused from JSP000865; JSP000896 uses its own project build directory.

Final original-to-candidate diff changes 27 source files (+198 / -122 lines), independently of repair attempt counts. Statement.lean remains byte-identical. Main.lean differs only by Nat.cast_one in one local proof simplifier; its exported statements are exact original bytes.

All failed attempts and their original logs remain preserved. This report selects only successful runs bound to the final source bytes. Full mathematical scope and construction review are separate evidence files in the parent verification directory.

## Changed source files

| File | Added lines | Removed lines |
|---|---:|---:|
| `JSP896/CellCounting.lean` | 11 | 4 |
| `JSP896/CellDeletion.lean` | 7 | 3 |
| `JSP896/CellStructure.lean` | 5 | 4 |
| `JSP896/CertificateIMC.lean` | 1 | 1 |
| `JSP896/CertificateSize.lean` | 6 | 3 |
| `JSP896/ClassTreeGrowth.lean` | 3 | 3 |
| `JSP896/CompatibleStars.lean` | 3 | 2 |
| `JSP896/CriticalEdge.lean` | 10 | 10 |
| `JSP896/DominationCertificate.lean` | 1 | 1 |
| `JSP896/ExpandedCells.lean` | 8 | 3 |
| `JSP896/FaithfulExtension.lean` | 24 | 13 |
| `JSP896/FeasibleExtension.lean` | 20 | 13 |
| `JSP896/FeasiblePair.lean` | 2 | 2 |
| `JSP896/FiniteTransversal.lean` | 18 | 11 |
| `JSP896/Main.lean` | 1 | 1 |
| `JSP896/MatchingCells.lean` | 2 | 2 |
| `JSP896/MatchingExchange.lean` | 37 | 19 |
| `JSP896/MatchingFacts.lean` | 3 | 1 |
| `JSP896/MatchingOrientationCentroid.lean` | 2 | 2 |
| `JSP896/OddComponentsReachability.lean` | 3 | 1 |
| `JSP896/OddComponentsSwitching.lean` | 10 | 6 |
| `JSP896/PairedCellTransversal.lean` | 1 | 1 |
| `JSP896/PairedDeficit.lean` | 1 | 0 |
| `JSP896/SharpnessChains.lean` | 11 | 9 |
| `JSP896/SharpnessTools.lean` | 4 | 4 |
| `JSP896/SmallCases.lean` | 3 | 2 |
| `JSP896/ThresholdAsymptotics.lean` | 1 | 1 |

## Full build and axiom logs

- `C:\Users\28983\Documents\ChatGPT\孙宇晨奖\THREE_LEAN_AUDITS_20261002\JSP000896\verification\build\full_lake_build_01.log`
- `C:\Users\28983\Documents\ChatGPT\孙宇晨奖\THREE_LEAN_AUDITS_20261002\JSP000896\verification\build\initial_axiom_audit_01.log`
- `C:\Users\28983\Documents\ChatGPT\孙宇晨奖\THREE_LEAN_AUDITS_20261002\JSP000896\verification\build\full_axiom_audit_01.log`

Exact source hashes, all 45 accepted module logs, dependency checks, all attempts and each axiom list are in FINAL_BUILD_RESULT.json. Final cumulative source diff is in FINAL_SOURCE_REPAIRS.patch.

## Source preservation checks

Normalized declaration headers and full structure fields match the originals in all 47 Lean files. The lexical normalization removes comments/strings and normalizes escaped simple identifiers such as partial to «partial», which denotes the same Lean field name. Main is additionally checked byte-for-byte except for the single Nat.cast_one proof-body insertion; Statement, root and both original audits match exactly.

The executable source scan removes nested comments and quoted strings before checking sorry, admit, axiom, native_decide, unsafe and sorryAx. This is supplementary source evidence alongside the actual axiom reports.

Repairs are proof-body API/elaboration fixes, explicit finite-set membership substitutions/sum identities, local real-valued cast corrections, and proof normalizations/name resolution. No original documentation was changed. Later root wrappers, public-runner reproduction and publication are outside this report.
