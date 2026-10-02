import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! Uniform scalar margins for the structure argument at every r≥5. -/

namespace JSP896

theorem structure_budget {r n d : ℝ} (hr : 5 ≤ r) (hd : 0 ≤ d)
    (hdeg : (2 * r - 4) * d < (r - 1) * n) :
    (4 * r - 5) * d < 2 * r * n := by
  have hrpos : 0 < 2 * r := by linarith
  have hr1 : 0 ≤ r - 1 := by linarith
  have hscaled := mul_lt_mul_of_pos_left hdeg hrpos
  have hnonneg : 0 ≤ (r - 5) * d := mul_nonneg (by linarith) hd
  by_contra h
  have hbad : 2 * r * n ≤ (4 * r - 5) * d := le_of_not_gt h
  have hbadscaled := mul_le_mul_of_nonneg_left hbad hr1
  nlinarith

theorem core_deficit_lt {r n d mass : ℝ}
    (hbudget : (4 * r - 5) * d < 2 * r * n)
    (hmass : 2 * r * n - (2 * r - 2) * d ≤ mass) :
    (2 * r - 2) * d - mass < d := by
  nlinarith

theorem expanded_cell_larger_than_exceptional_bound {r n d : ℝ}
    (hbudget : (4 * r - 5) * d < 2 * r * n) :
    (2 * r - 2) * d - r * n < r * n - (2 * r - 3) * d := by
  nlinarith

end JSP896
