
## 001_finite_transversal_elaboration: JSP896.FiniteTransversal

Avoid rcases rfl substituting shared insertion vertex across branches; supply reflexive card comparison explicitly. Statements unchanged.

Diagnostic: verification/build/first_01_JSP896_FiniteTransversal.log; before/after/diff: verification/repairs/001_finite_transversal_elaboration.

## 002_mul_sum_api: JSP896.PairedDeficit

Use pinned Mathlib global mul_sum after API namespace migration; theorem unchanged.

Diagnostic: verification/build/third_02_JSP896_PairedDeficit.log; before/after/diff: verification/repairs/002_mul_sum_api.

## 003_explicit_ring_finset_import: JSP896.PairedDeficit

Add explicit Ring.Finset dependency providing Finset.mul_sum, absent from original imports; restore correct namespace. Theorem unchanged.

Diagnostic: verification/build/fourth_02_JSP896_PairedDeficit.log; before/after/diff: verification/repairs/003_explicit_ring_finset_import.

## 004_keyword_field_and_empty_api: JSP896.FeasiblePair

Escape Lean reserved keyword partial as structure field without changing name/type; use current Finset.notMem_empty API.

Diagnostic: verification/build/fifth_04_JSP896_FeasiblePair.log; before/after/diff: verification/repairs/004_keyword_field_and_empty_api.

## 005_explicit_insert_substitution: JSP896.CompatibleStars

Explicitly substitute inserted element v rather than shared star center w. Statement unchanged.

Diagnostic: verification/build/sixth_06_JSP896_CompatibleStars.log; before/after/diff: verification/repairs/005_explicit_insert_substitution.

## 006_current_set_edge_api: JSP896.ClassTreeGrowth

Use current notMem theorem spelling and all explicit edge_adj vertex arguments; graph/tree statement unchanged.

Diagnostic: verification/build/seventh_07_JSP896_ClassTreeGrowth.log; before/after/diff: verification/repairs/006_current_set_edge_api.

## 007_preserve_common_star_center: JSP896.FaithfulExtension

Explicitly substitute endpoint x/y (including primed copies), retaining common center c across every case. Literal faithful-edge/tree statements unchanged.

Diagnostic: verification/build/eighth_08_JSP896_FaithfulExtension.log; before/after/diff: verification/repairs/007_preserve_common_star_center.

## 008_correct_substitution_layout: JSP896.FaithfulExtension

Correct repair script indentation and restrict endpoint substitutions to two-field vertex cases; retain three-field class equality cases. No theorem statement changes.

Diagnostic: verification/build/ninth_08_JSP896_FaithfulExtension.log; before/after/diff: verification/repairs/008_correct_substitution_layout.

## 009_extension_center_substitution: JSP896.FeasibleExtension

Preserve common extension center c by explicitly substituting x/y/z in insertion cases; mathematical extension invariants unchanged.

Diagnostic: verification/build/tenth_09_JSP896_FeasibleExtension.log; before/after/diff: verification/repairs/009_extension_center_substitution.

## 010_image_subset_api: JSP896.DominationCertificate

Use current image monotonicity lemma name; domination statement unchanged.

Diagnostic: verification/build/eleventh_10_JSP896_DominationCertificate.log; before/after/diff: verification/repairs/010_image_subset_api.

## 011_image_map_implicit_argument: JSP896.DominationCertificate

Specify image function by its current implicit named argument, rather than obsolete explicit position; theorem unchanged.

Diagnostic: verification/build/twelfth_10_JSP896_DominationCertificate.log; before/after/diff: verification/repairs/011_image_map_implicit_argument.

## 012_induced_card_and_inherited_darts: JSP896.CertificateSize

Make induced-card equality type explicit before transport; inherited Dart product projections expressed as typed lambdas. Statements unchanged.

Diagnostic: verification/build/thirteenth_11_JSP896_CertificateSize.log; before/after/diff: verification/repairs/012_induced_card_and_inherited_darts.

## 013_subtype_fintype_transport: JSP896.CertificateSize

Transport equality between extensionally identical finite subtype instances supplied by FinsetCoe.fintype versus Subtype.fintype; statements unchanged.

Diagnostic: verification/build/fourteenth_11_JSP896_CertificateSize.log; before/after/diff: verification/repairs/013_subtype_fintype_transport.

## 014_edge_finset_extensionality: JSP896.CertificateSize

Finish instance transport by edge-finset extensionality, whose membership is literal adjacency and independent of Fintype enumeration.

Diagnostic: verification/build/fifteenth_11_JSP896_CertificateSize.log; before/after/diff: verification/repairs/014_edge_finset_extensionality.

## 015_nat_sum_constant_cast: JSP896.CertificateIMC

Normalize redundant Nat-to-Nat cardinal cast in constant fiber sum, preserving numerical and certificate statements.

Diagnostic: verification/build/sixteenth_15_JSP896_CertificateIMC.log; before/after/diff: verification/repairs/015_nat_sum_constant_cast.

## 016_classical_edge_statement_darts: JSP896.MatchingFacts

Scope classical finite edge-set instances for theorem statements and use inherited Dart projections through typed lambdas. No mathematical statement changes.

Diagnostic: verification/build/eighteenth_20_JSP896_MatchingFacts.log; before/after/diff: verification/repairs/016_classical_edge_statement_darts.

## 017_parenthesize_sum_body: JSP896.PairedCellTransversal

Parenthesize finite-sum subtraction body to keep i in binder scope; theorem statements unchanged.

Diagnostic: verification/build/nineteenth_21_JSP896_PairedCellTransversal.log; before/after/diff: verification/repairs/017_parenthesize_sum_body.

## 018_reachable_simp_closes_goal: JSP896.MatchingCells

Avoid an extra tactic after rw reduces reflexive reachability and closes the goal automatically; literal class-cut construction unchanged.

Diagnostic: verification/build/twentieth_23_JSP896_MatchingCells.log; before/after/diff: verification/repairs/018_reachable_simp_closes_goal.

## 019_explicit_exchange_edge_cases: JSP896.MatchingExchange

Explicit endpoint substitutions preserve centers/classes; avoid shadowing vertex and class inequalities; apply edge adjacency before simp normalizes reflexive equalities; update empty membership spelling. All exchange statements unchanged.

Diagnostic: verification/build/twentyfirst_24_JSP896_MatchingExchange.log; before/after/diff: verification/repairs/019_explicit_exchange_edge_cases.

## 020_counting_simp_scope_and_cast: JSP896.CellCounting

Avoid extra omega after rw closes numeral comparison; use controlled indicator-card simp to prevent unfolding cell predicate; normalize Nat.cast_id. Mathematical counting statements unchanged.

Diagnostic: verification/build/twentysecond_25_JSP896_CellCounting.log; before/after/diff: verification/repairs/020_counting_simp_scope_and_cast.

## 021_indicator_filter_identity: JSP896.CellCounting

Prove filtered universe equals the original counted finset before applying indicator sum; normalize Nat cast rather than applying ext to a cardinal.

Diagnostic: verification/build/twentythird_25_JSP896_CellCounting.log; before/after/diff: verification/repairs/021_indicator_filter_identity.

## 022_sigma_cast_removed_sum_symmetry: JSP896.CellDeletion

Expose dependent Sigma value equality before transport, unfold local cast-valued removal function before mod_cast, and explicitly reverse negated equality. Residual-cell construction unchanged.

Diagnostic: verification/build/twentyfourth_26_JSP896_CellDeletion.log; before/after/diff: verification/repairs/022_sigma_cast_removed_sum_symmetry.

## 023_control_small_set_sum_rewrites: JSP896.ExpandedCells

Rewrite two/three-cell sums using explicit distinctness proofs and sum_pair, avoiding unrestricted simplification of deficits into rearranged arithmetic. All expanded-cell statements unchanged.

Diagnostic: verification/build/twentyfifth_27_JSP896_ExpandedCells.log; before/after/diff: verification/repairs/023_control_small_set_sum_rewrites.

## 024_real_local_ite_and_pair_endpoint: JSP896.CellStructure

Annotate local conditional cardinal branches as real to avoid unintended Nat subtraction/cast during ring reasoning; retain counted endpoint x using explicit substitution. Exported declarations and model definitions unchanged.

Diagnostic: verification/build/twentysixth_28_JSP896_CellStructure.log; before/after/diff: verification/repairs/024_real_local_ite_and_pair_endpoint.

## 025_main_cast_one_normalization: JSP896.Main

Normalize the cast of the natural constant one before nlinarith. The sole change is in the local hstructure proof; every exported theorem statement, definition and parameter remains unchanged.

Diagnostic: verification/build/twentyseventh_44_JSP896_Main.log; before/after/diff: verification/repairs/025_main_cast_one_normalization.
