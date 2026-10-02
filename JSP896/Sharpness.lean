import JSP896.SharpnessChains

/-!
# Literal sharpness for every positive class size

This implements Szabó--Tardos, Construction 3.3, including every integer
remainder and the isolated-class padding.  There are no divisibility premises.

Project pins: Lean 4.35.0-rc3; Mathlib
2a885768dae569d938bb9ff3474da6a8753bb90a.
Complete proof source; pinned compilation and audit records are in VERIFICATION.md.
-/

namespace JSP896
namespace Sharpness

/-- Exact positive-remainder division for Construction 3.3.
The last equality is the size of each leftover class. -/
theorem rounding_data {k n d : ℕ} (hk : 0 < k) (hd : 0 < d)
    (hdn : d < n) (hthreshold : k * n ≤ (2 * k - 1) * d) :
    ∃ q i a u : ℕ,
      q = (d - 1) / (2 * d - n) ∧ i = 2 * d - n ∧ a = n - d ∧
      u = d - q * i ∧
      0 < q ∧ q < k ∧ 0 < i ∧ 0 < u ∧ u ≤ i ∧
      d = q * i + u ∧ d = a + i ∧ n = d + a ∧
      a ≤ q * i ∧ n = d + (q - 1) * i + u := by
  have hcoef : (2 * k - 1) * d + d = 2 * k * d := by
    calc
      (2 * k - 1) * d + d = (2 * k - 1 + 1) * d := by ring
      _ = 2 * k * d := by rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * k)]
  have hbudget : k * n + d ≤ 2 * k * d := by omega
  have hn2d : n < 2 * d := by
    by_contra h
    have hmul := Nat.mul_le_mul_left k (show 2 * d ≤ n by omega)
    nlinarith
  let i := 2 * d - n
  let a := n - d
  let q := (d - 1) / i
  let u := d - q * i
  have hi : 0 < i := by dsimp only [i]; omega
  have ha : 0 < a := by dsimp only [a]; omega
  have hdai : d = a + i := by dsimp only [a, i]; omega
  have hnda : n = d + a := by dsimp only [a]; omega
  have hni : n + i = 2 * d := by dsimp only [i]; omega
  have hsum : k * n + k * i = 2 * k * d := by
    calc
      k * n + k * i = k * (n + i) := by ring
      _ = k * (2 * d) := by rw [hni]
      _ = 2 * k * d := by ring
  have hdki : d ≤ k * i := by omega
  have hqpos : 0 < q := by
    dsimp only [q]
    exact Nat.div_pos (by omega) hi
  have hqk : q < k := by
    dsimp only [q]
    apply (Nat.div_lt_iff_lt_mul hi).mpr
    omega
  have hqmul : q * i ≤ d - 1 := by
    exact Nat.div_mul_le_self (d - 1) i
  have hqmulLt : q * i < d := by omega
  have hdecomp : (d - 1) % i + q * i = d - 1 := by
    simpa only [q, Nat.mul_comm] using Nat.mod_add_div (d - 1) i
  have hmod : (d - 1) % i < i := Nat.mod_lt _ hi
  have hu : 0 < u := by dsimp only [u]; omega
  have hdu : d = q * i + u := by dsimp only [u]; omega
  have hui : u ≤ i := by omega
  have hcapacity : a ≤ q * i := by omega
  have hqstep : q * i = (q - 1) * i + i := by
    calc
      q * i = (q - 1 + 1) * i := by rw [Nat.sub_add_cancel hqpos]
      _ = (q - 1) * i + i := by ring
  have hleftover : n = d + (q - 1) * i + u := by omega
  exact ⟨q, i, a, u, rfl, rfl, rfl, rfl, hqpos, hqk, hi, hu, hui,
    hdu, hdai, hnda, hcapacity, hleftover⟩

end Sharpness

/-- The actual even-part sharpness graph.  Every class has exactly `n`
vertices, every degree is at most `d`, and no independent transversal exists.
This includes `n ≤ d`, arbitrary positive remainders, and all padding cases. -/
theorem exists_sharpness_even (k n d : ℕ)
    (hk : 0 < k) (_hn : 0 < n) (hd : 0 < d)
    (hthreshold : k * n ≤ (2 * k - 1) * d) :
    ∃ G : SimpleGraph (Vertex (2 * k) n), IsPartite G ∧
      (∀ v, degree G v ≤ d) ∧ ¬ HasIndependentTransversal G := by
  by_cases hnd : n ≤ d
  · exact Sharpness.exists_small_example (by omega) hnd
  · obtain ⟨q, i, a, u, hqformula, hiformula, haformula, huformula,
      hqpos, hqk, hi, hu, hui, hdu, hdai, hnda, hcapacity, hleftover⟩ :=
      Sharpness.rounding_data hk hd (by omega) hthreshold
    obtain ⟨G, hpart, hdegree, hno⟩ :=
      Sharpness.exists_chain_example hi hdai hnda hcapacity
    exact Sharpness.pad_example (by omega) (by omega) G hpart hdegree hno

/-- One extra independent class extends the even example to an odd number
of classes without altering any old adjacency or degree. -/
theorem exists_sharpness_odd (k n d : ℕ)
    (hk : 0 < k) (hn : 0 < n) (hd : 0 < d)
    (hthreshold : k * n ≤ (2 * k - 1) * d) :
    ∃ G : SimpleGraph (Vertex (2 * k + 1) n), IsPartite G ∧
      (∀ v, degree G v ≤ d) ∧ ¬ HasIndependentTransversal G := by
  obtain ⟨G, hpart, hdegree, hno⟩ :=
    exists_sharpness_even k n d hk hn hd hthreshold
  exact Sharpness.pad_example (by omega) (by omega) G hpart hdegree hno

/-- Uniform floor-parameter export used by the exact threshold adapter. -/
theorem exists_sharpness_all (r n d : ℕ)
    (hr : 2 ≤ r) (hn : 0 < n) (hd : 0 < d)
    (hthreshold : (r / 2) * n ≤ (2 * (r / 2) - 1) * d) :
    ∃ G : SimpleGraph (Vertex r n), IsPartite G ∧
      (∀ v, degree G v ≤ d) ∧ ¬ HasIndependentTransversal G := by
  have hk : 0 < r / 2 := Nat.div_pos hr (by norm_num)
  obtain ⟨G, hpart, hdegree, hno⟩ :=
    exists_sharpness_even (r / 2) n d hk hn hd hthreshold
  apply Sharpness.pad_example (by omega) _ G hpart hdegree hno
  have h := Nat.div_mul_le_self r 2
  omega

end JSP896
