import JSP896.ThresholdArithmetic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic

/-!
# Fixed-class and large-class threshold limits

These are limits of the explicit integer formulas. The final named bridge
takes `FullResolution` explicitly; `JSP896.Main` discharges that argument using
the finite graph proof. Formula limits alone do not imply graph sufficiency.
Pinned compilation and audit records are in VERIFICATION.md.
-/

namespace JSP896

open Filter
open scoped Topology

noncomputable def independentCoefficient (r : ℕ) : ℝ :=
  ((r / 2 : ℕ) : ℝ) / ((2 * (r / 2) - 1 : ℕ) : ℝ)

noncomputable def cliqueCoefficient (r : ℕ) : ℝ :=
  ((r - 1 : ℕ) : ℝ) - independentCoefficient r

/-- The ceiling changes the normalized value by at most 1/n. -/
theorem normalized_independentThreshold_bounds (r n : ℕ)
    (hr : 2 ≤ r) (hn : 0 < n) :
    independentCoefficient r ≤ (independentThreshold r n : ℝ) / n ∧
    (independentThreshold r n : ℝ) / n ≤ independentCoefficient r + 1 / n := by
  let k : ℝ := ((r / 2 : ℕ) : ℝ)
  let b : ℝ := ((2 * (r / 2) - 1 : ℕ) : ℝ)
  let D : ℝ := (independentThreshold r n : ℝ)
  have hb : 0 < b := by
    dsimp only [b]
    exact_mod_cast threshold_denominator_pos hr
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnat := independentThreshold_sandwich r n hr
  have hl : k * (n : ℝ) ≤ b * D := by
    dsimp only [k, b, D]
    exact_mod_cast hnat.1
  have hu : b * D ≤ k * (n : ℝ) + b := by
    dsimp only [k, b, D]
    exact_mod_cast hnat.2
  have hl' : k * (n : ℝ) / b ≤ D :=
    (div_le_iff₀ hb).mpr (by nlinarith)
  have hu' : D ≤ k * (n : ℝ) / b + 1 := by
    calc
      D ≤ (k * (n : ℝ) + b) / b := (le_div_iff₀ hb).mpr (by nlinarith)
      _ = k * (n : ℝ) / b + 1 := by field_simp [hb.ne'] <;> ring
  change k / b ≤ D / (n : ℝ) ∧ D / (n : ℝ) ≤ k / b + 1 / (n : ℝ)
  constructor
  · calc
      k / b = (k * (n : ℝ) / b) / (n : ℝ) := by field_simp [hb.ne', hnR.ne'] <;> ring
      _ ≤ D / (n : ℝ) := div_le_div_of_nonneg_right hl' hnR.le
  · calc
      D / (n : ℝ) ≤ (k * (n : ℝ) / b + 1) / (n : ℝ) :=
        div_le_div_of_nonneg_right hu' hnR.le
      _ = k / b + 1 / (n : ℝ) := by field_simp [hb.ne', hnR.ne'] <;> ring

/-- For each fixed r≥2, the exact independent threshold divided by n
converges to floor(r/2)/(2 floor(r/2)-1). -/
theorem fixed_r_threshold_limit (r : ℕ) (hr : 2 ≤ r) :
    Tendsto (fun n : ℕ => (independentThreshold r n : ℝ) / n)
      atTop (𝓝 (independentCoefficient r)) := by
  have hupper : Tendsto (fun n : ℕ => independentCoefficient r + 1 / (n : ℝ))
      atTop (𝓝 (independentCoefficient r)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds (x := independentCoefficient r)).add
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact (normalized_independentThreshold_bounds r n hr (by omega)).1
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact (normalized_independentThreshold_bounds r n hr (by omega)).2

theorem normalized_cliqueThreshold_eq (r n : ℕ)
    (hr : 2 ≤ r) (hn : 0 < n) :
    (cliqueThreshold r n : ℝ) / n =
      ((r - 1 : ℕ) : ℝ) - (independentThreshold r n : ℝ) / n := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hsum : (cliqueThreshold r n : ℝ) + (independentThreshold r n : ℝ) =
      ((r - 1 : ℕ) : ℝ) * (n : ℝ) := by
    exact_mod_cast cliqueThreshold_add_independentThreshold r n hr
  apply (div_eq_iff hnR).mpr
  calc
    (cliqueThreshold r n : ℝ) =
        ((r - 1 : ℕ) : ℝ) * (n : ℝ) - (independentThreshold r n : ℝ) := by linarith
    _ = (((r - 1 : ℕ) : ℝ) - (independentThreshold r n : ℝ) / n) * n := by
      field_simp [hnR] <;> ring

/-- The corresponding fixed-r normalized clique-threshold limit. -/
theorem fixed_r_cliqueThreshold_limit (r : ℕ) (hr : 2 ≤ r) :
    Tendsto (fun n : ℕ => (cliqueThreshold r n : ℝ) / n)
      atTop (𝓝 (cliqueCoefficient r)) := by
  have hlim : Tendsto
      (fun n : ℕ => ((r - 1 : ℕ) : ℝ) - (independentThreshold r n : ℝ) / n)
      atTop (𝓝 (cliqueCoefficient r)) := by
    exact (tendsto_const_nhds (x := ((r - 1 : ℕ) : ℝ))).sub
      (fixed_r_threshold_limit r hr)
  have heq :
      (fun n : ℕ => ((r - 1 : ℕ) : ℝ) - (independentThreshold r n : ℝ) / n)
        =ᶠ[atTop] (fun n : ℕ => (cliqueThreshold r n : ℝ) / n) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact (normalized_cliqueThreshold_eq r n hr (by omega)).symm
  exact Filter.Tendsto.congr' heq hlim

theorem fixed_r_clique_excess_limit (r : ℕ) (hr : 2 ≤ r) :
    Tendsto (fun n : ℕ => ((r - 1 : ℕ) : ℝ) - (cliqueThreshold r n : ℝ) / n)
      atTop (𝓝 (independentCoefficient r)) := by
  have h := (tendsto_const_nhds (x := ((r - 1 : ℕ) : ℝ))).sub
    (fixed_r_cliqueThreshold_limit r hr)
  simpa only [cliqueCoefficient, sub_sub_cancel] using h

theorem half_parts_tendsto_atTop : Tendsto (fun r : ℕ => r / 2) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨2 * b, fun r hr => ?_⟩
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
  omega

theorem independentCoefficient_eq_real_quotient (r : ℕ) (hr : 2 ≤ r) :
    independentCoefficient r =
      ((r / 2 : ℕ) : ℝ) / (2 * ((r / 2 : ℕ) : ℝ) - 1) := by
  have hk := half_parts_pos hr
  have hcast : ((2 * (r / 2) - 1 : ℕ) : ℝ) =
      2 * ((r / 2 : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * (r / 2))]
    push_cast <;> ring
  simp only [independentCoefficient, hcast]

/-- The original large-number-of-classes coefficient tends to one half. -/
theorem large_r_ratio_limit :
    Tendsto independentCoefficient atTop (𝓝 (1 / 2 : ℝ)) := by
  have hraw : Tendsto (fun k : ℕ => (k : ℝ) / (2 * (k : ℝ) - 1))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    have h := tendsto_add_mul_div_add_mul_atTop_nhds
      (0 : ℝ) (-1) 1 (d := 2) (by norm_num)
    simpa only [zero_add, add_zero, one_mul, sub_eq_add_neg, add_comm] using h
  have hcompose := hraw.comp half_parts_tendsto_atTop
  have heq : (fun r : ℕ => ((r / 2 : ℕ) : ℝ) /
      (2 * ((r / 2 : ℕ) : ℝ) - 1)) =ᶠ[atTop] independentCoefficient := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with r hr
    exact (independentCoefficient_eq_real_quotient r hr).symm
  exact Filter.Tendsto.congr' heq hcompose

/-- Equivalent original large-r statement in clique-threshold language. -/
theorem large_r_clique_excess_limit :
    Tendsto (fun r : ℕ => ((r - 1 : ℕ) : ℝ) - cliqueCoefficient r)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  simpa only [cliqueCoefficient, sub_sub_cancel] using large_r_ratio_limit

/-- Explicit assembly bridge.  This theorem requires the full finite graph
resolution as a visible argument; the graph proof is never inferred from
formula limits.  Once supplied, it records both requested asymptotic regimes
together with the original finite graph conclusion. -/
theorem fullResolution_with_asymptotics (hfull : FullResolution) :
    FullResolution ∧
    (∀ r : ℕ, 2 ≤ r →
      Tendsto (fun n : ℕ => (independentThreshold r n : ℝ) / n)
        atTop (𝓝 (independentCoefficient r)) ∧
      Tendsto (fun n : ℕ => (cliqueThreshold r n : ℝ) / n)
        atTop (𝓝 (cliqueCoefficient r))) ∧
    Tendsto independentCoefficient atTop (𝓝 (1 / 2 : ℝ)) ∧
    Tendsto (fun r : ℕ => ((r - 1 : ℕ) : ℝ) - cliqueCoefficient r)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  exact ⟨hfull, fun r hr => ⟨fixed_r_threshold_limit r hr,
    fixed_r_cliqueThreshold_limit r hr⟩,
    large_r_ratio_limit, large_r_clique_excess_limit⟩

end JSP896
