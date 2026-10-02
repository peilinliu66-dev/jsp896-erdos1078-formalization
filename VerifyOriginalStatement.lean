import JSP896

/-!
Expanded checks of the original finite graph statements and both asymptotic
regimes. All declarations below are proved from the project's actual exported
theorems; no source-paper theorem, graph certificate, or extra assumption is
introduced. The BES large-r formulation c_r - (r - 2) is stated literally.
-/

open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable

theorem audit_literal_finite_clique_resolution :
    ∀ r n : ℕ, 2 ≤ r → 0 < n →
      (∀ G : SimpleGraph (Fin r × Fin n),
        (∀ ⦃v w⦄, G.Adj v w → v.1 ≠ w.1) →
        (∀ v, (r - 1) * n -
          (((r / 2) * n + (2 * (r / 2) - 1) - 1) / (2 * (r / 2) - 1)) <
          (Finset.univ.filter (G.Adj v)).card) →
        ∃ f : Fin r → Fin n, ∀ i j, i ≠ j → G.Adj (i, f i) (j, f j)) ∧
      ∃ G : SimpleGraph (Fin r × Fin n),
        (∀ ⦃v w⦄, G.Adj v w → v.1 ≠ w.1) ∧
        (∀ v, (r - 1) * n -
          (((r / 2) * n + (2 * (r / 2) - 1) - 1) / (2 * (r / 2) - 1)) ≤
          (Finset.univ.filter (G.Adj v)).card) ∧
        ¬ (∃ f : Fin r → Fin n, ∀ i j, i ≠ j → G.Adj (i, f i) (j, f j)) := by
  classical
  simpa only [JSP896.FullResolution, JSP896.Vertex, JSP896.IsPartite,
    JSP896.cliqueThreshold, JSP896.independentThreshold, JSP896.degree,
    JSP896.neighbors, JSP896.HasTransversalClique] using JSP896.full_resolution

theorem audit_literal_independent_sufficiency :
    ∀ r n : ℕ, 2 ≤ r → 0 < n →
      ∀ G : SimpleGraph (Fin r × Fin n),
        (∀ ⦃v w⦄, G.Adj v w → v.1 ≠ w.1) →
        (∀ v, (Finset.univ.filter (G.Adj v)).card <
          (((r / 2) * n + (2 * (r / 2) - 1) - 1) / (2 * (r / 2) - 1))) →
        ∃ f : Fin r → Fin n, ∀ i j, i ≠ j → ¬ G.Adj (i, f i) (j, f j) := by
  classical
  simpa only [JSP896.Vertex, JSP896.IsPartite, JSP896.independentThreshold,
    JSP896.degree, JSP896.neighbors, JSP896.HasIndependentTransversal] using
    JSP896.independentTransversal_of_degree_lt_threshold

theorem audit_literal_fixed_r_limits :
    ∀ r : ℕ, 2 ≤ r →
      Tendsto (fun n : ℕ =>
        ((((r / 2) * n + (2 * (r / 2) - 1) - 1) /
          (2 * (r / 2) - 1) : ℕ) : ℝ) / n)
        atTop (𝓝 (((r / 2 : ℕ) : ℝ) / ((2 * (r / 2) - 1 : ℕ) : ℝ))) ∧
      Tendsto (fun n : ℕ =>
        (((r - 1) * n -
          (((r / 2) * n + (2 * (r / 2) - 1) - 1) /
            (2 * (r / 2) - 1)) : ℕ) : ℝ) / n)
        atTop (𝓝 (((r - 1 : ℕ) : ℝ) -
          ((r / 2 : ℕ) : ℝ) / ((2 * (r / 2) - 1 : ℕ) : ℝ))) := by
  simpa only [JSP896.independentThreshold, JSP896.cliqueThreshold,
    JSP896.independentCoefficient, JSP896.cliqueCoefficient] using
    JSP896.full_resolution_with_original_limits.2.1

theorem audit_literal_large_r_independent_limit :
    Tendsto (fun r : ℕ => ((r / 2 : ℕ) : ℝ) /
      ((2 * (r / 2) - 1 : ℕ) : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := by
  exact JSP896.full_resolution_with_original_limits.2.2.1

/-- The original BES expression c_r - (r - 2), using literal explicit c_r. -/
theorem audit_literal_original_BES_large_r_limit :
    Tendsto (fun r : ℕ =>
      (((r - 1 : ℕ) : ℝ) -
        ((r / 2 : ℕ) : ℝ) / ((2 * (r / 2) - 1 : ℕ) : ℝ)) -
        ((r - 2 : ℕ) : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hlimit : Tendsto (fun r : ℕ => 1 - JSP896.independentCoefficient r)
      atTop (𝓝 (1 / 2 : ℝ)) := by
    convert (tendsto_const_nhds (x := (1 : ℝ))).sub
      JSP896.full_resolution_with_original_limits.2.2.1 using 1 <;> norm_num
  apply Filter.Tendsto.congr' _ hlimit
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with r hr
  have hcast : ((r - 1 : ℕ) : ℝ) - ((r - 2 : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_sub (by omega : 2 ≤ r)]
    push_cast
    ring
  dsimp only [JSP896.independentCoefficient]
  linarith

#check audit_literal_finite_clique_resolution
#check audit_literal_independent_sufficiency
#check audit_literal_fixed_r_limits
#check audit_literal_large_r_independent_limit
#check audit_literal_original_BES_large_r_limit
#check JSP896.full_resolution_with_original_limits

#print axioms audit_literal_finite_clique_resolution
#print axioms audit_literal_independent_sufficiency
#print axioms audit_literal_fixed_r_limits
#print axioms audit_literal_large_r_independent_limit
#print axioms audit_literal_original_BES_large_r_limit
#print axioms JSP896.full_resolution_with_original_limits
