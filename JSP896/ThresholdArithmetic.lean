import JSP896.Complement
import JSP896.Sharpness

/-!
# Exact integer ceiling and literal sharpness adapters

No sufficiency theorem is assumed in this file.  The sharpness exports use the
actual graph construction from `Sharpness`.  Pinned execution records are in VERIFICATION.md.
-/

namespace JSP896

private theorem lt_natCeilDiv_iff (a b d : ℕ) (hb : 0 < b) :
    d < (a + b - 1) / b ↔ b * d < a := by
  have hnum : a + b - 1 + 1 = a + b := by omega
  have hprod : (d + 1) * b = b * d + b := by ring
  constructor
  · intro h
    have hmul : (d + 1) * b ≤ a + b - 1 :=
      (Nat.le_div_iff_mul_le hb).mp (by omega)
    omega
  · intro h
    have hmul : (d + 1) * b ≤ a + b - 1 := by omega
    have hle := (Nat.le_div_iff_mul_le hb).mpr hmul
    omega

private theorem le_mul_natCeilDiv (a b : ℕ) (hb : 0 < b) :
    a ≤ b * ((a + b - 1) / b) := by
  have hdiv := Nat.div_add_mod (a + b - 1) b
  have hmod := Nat.mod_lt (a + b - 1) hb
  have hnum : a + b - 1 + 1 = a + b := by omega
  omega

theorem half_parts_pos {r : ℕ} (hr : 2 ≤ r) : 0 < r / 2 :=
  Nat.div_pos hr (by norm_num)

theorem threshold_denominator_pos {r : ℕ} (hr : 2 ≤ r) :
    0 < 2 * (r / 2) - 1 := by
  have h := half_parts_pos hr
  omega

/-- Exact strict integer ceiling equivalence; valid also for n=0. -/
theorem lt_independentThreshold_iff (r n d : ℕ) (hr : 2 ≤ r) :
    d < independentThreshold r n ↔
      (2 * (r / 2) - 1) * d < (r / 2) * n := by
  exact lt_natCeilDiv_iff _ _ _ (threshold_denominator_pos hr)

theorem independentThreshold_mul_ge (r n : ℕ) (hr : 2 ≤ r) :
    (r / 2) * n ≤ (2 * (r / 2) - 1) * independentThreshold r n := by
  exact le_mul_natCeilDiv _ _ (threshold_denominator_pos hr)

theorem independentThreshold_pos {r n : ℕ} (hr : 2 ≤ r) (hn : 0 < n) :
    0 < independentThreshold r n := by
  apply (lt_independentThreshold_iff r n 0 hr).mpr
  simpa only [Nat.mul_zero] using Nat.mul_pos (half_parts_pos hr) hn

theorem independentThreshold_le_n (r n : ℕ) (hr : 2 ≤ r) :
    independentThreshold r n ≤ n := by
  have hk := half_parts_pos hr
  have hcoef : r / 2 ≤ 2 * (r / 2) - 1 := by omega
  have hmul := Nat.mul_le_mul_right n hcoef
  by_contra h
  have hlt := (lt_independentThreshold_iff r n n hr).mp (by omega)
  omega

theorem independentThreshold_le_capacity (r n : ℕ) (hr : 2 ≤ r) :
    independentThreshold r n ≤ (r - 1) * n := by
  apply (independentThreshold_le_n r n hr).trans
  have hmul := Nat.mul_le_mul_right n (show 1 ≤ r - 1 by omega)
  simpa only [one_mul] using hmul

theorem cliqueThreshold_add_independentThreshold (r n : ℕ) (hr : 2 ≤ r) :
    cliqueThreshold r n + independentThreshold r n = (r - 1) * n := by
  exact Nat.sub_add_cancel (independentThreshold_le_capacity r n hr)

@[simp] theorem independentThreshold_two (n : ℕ) : independentThreshold 2 n = n := by
  simp [independentThreshold]

@[simp] theorem independentThreshold_three (n : ℕ) : independentThreshold 3 n = n := by
  simp [independentThreshold]

theorem degree_lt_independentThreshold_iff {r n : ℕ}
    (G : SimpleGraph (Vertex r n)) (v : Vertex r n) (hr : 2 ≤ r) :
    degree G v < independentThreshold r n ↔
      (2 * (r / 2) - 1) * degree G v < (r / 2) * n :=
  lt_independentThreshold_iff r n (degree G v) hr

theorem complement_lt_independentThreshold_iff {r n : ℕ}
    (G : SimpleGraph (Vertex r n)) (hpart : IsPartite G)
    (v : Vertex r n) (hr : 2 ≤ r) :
    degree (crossComplement G) v < independentThreshold r n ↔
      cliqueThreshold r n < degree G v :=
  complement_degree_lt_iff G hpart v (independentThreshold_le_capacity r n hr)

/-- A genuine extremal graph at the exact ceiling, proved independently of
the sufficiency argument. -/
theorem exists_independent_sharpness_at_threshold (r n : ℕ)
    (hr : 2 ≤ r) (hn : 0 < n) :
    ∃ G : SimpleGraph (Vertex r n), IsPartite G ∧
      (∀ v, degree G v ≤ independentThreshold r n) ∧
      ¬ HasIndependentTransversal G :=
  exists_sharpness_all r n (independentThreshold r n) hr hn
    (independentThreshold_pos hr hn) (independentThreshold_mul_ge r n hr)

/-- Literal clique-form sharpness, obtained by cross-part complementation. -/
theorem exists_sharpness_at_threshold (r n : ℕ)
    (hr : 2 ≤ r) (hn : 0 < n) :
    ∃ G : SimpleGraph (Vertex r n), IsPartite G ∧
      (∀ v, cliqueThreshold r n ≤ degree G v) ∧
      ¬ HasTransversalClique G := by
  obtain ⟨H, hpart, hdegree, hno⟩ := exists_independent_sharpness_at_threshold r n hr hn
  refine ⟨crossComplement H, crossComplement_isPartite H, ?_, ?_⟩
  · intro v
    have hsum := degree_add_complement H hpart v
    have hle := hdegree v
    have hthreshold := cliqueThreshold_add_independentThreshold r n hr
    omega
  · intro h
    exact hno ((clique_crossComplement_iff H).mp h)

/-- Multiplicative ceiling sandwich.  The upper slack is at most one
denominator; it is the only error term used by the limit adapters. -/
theorem independentThreshold_sandwich (r n : ℕ) (hr : 2 ≤ r) :
    (r / 2) * n ≤ (2 * (r / 2) - 1) * independentThreshold r n ∧
    (2 * (r / 2) - 1) * independentThreshold r n ≤
      (r / 2) * n + (2 * (r / 2) - 1) := by
  refine ⟨independentThreshold_mul_ge r n hr, ?_⟩
  have h := Nat.div_mul_le_self
    ((r / 2) * n + (2 * (r / 2) - 1) - 1) (2 * (r / 2) - 1)
  change (2 * (r / 2) - 1) *
    (((r / 2) * n + (2 * (r / 2) - 1) - 1) / (2 * (r / 2) - 1)) ≤ _
  rw [Nat.mul_comm] at h
  exact h.trans (Nat.sub_le _ _)

end JSP896
