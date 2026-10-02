import JSP896.CertificateMatching
import Mathlib.Tactic.NormNum

/-! The full-class induced matching certificate, derived from finite maximality
and the sharp strict degree hypothesis. No certificate-existence premise is
exported by the final theorem of this file. -/

namespace JSP896.FeasiblePair

open FiniteTransversal FiniteGraphCounting
open scoped BigOperators

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]

theorem smaller_active_set_impossible {q r n d : ℝ}
    (hq : 0 < q) (hr : 3 ≤ r) (hqr : q ≤ r - 1) (hd : 0 ≤ d)
    (hdom : q * n ≤ 2 * (q - 1) * d)
    (hdeg : (2 * r - 4) * d < (r - 1) * n) : False := by
  have h₁ := mul_le_mul_of_nonneg_left hdom (show 0 ≤ r - 1 by linarith)
  have h₂ := mul_lt_mul_of_pos_left hdeg hq
  have hgap : 0 ≤ 2 * (r - 1 - q) * d :=
    mul_nonneg (by linarith) hd
  nlinarith

theorem matching_budget {r n d : ℝ} (hr : 3 ≤ r) (hd : 0 ≤ d)
    (hdeg : (2 * r - 4) * d < (r - 1) * n) :
    (2 * r - 3) * d < r * n := by
  have h₁ := mul_lt_mul_of_pos_left hdeg (show 0 < r by linarith)
  have hgap : 0 ≤ (r - 3) * d := mul_nonneg (by linarith) hd
  by_contra h
  have h₂ := mul_le_mul_of_nonneg_left (le_of_not_gt h)
    (show 0 ≤ r - 1 by linarith)
  nlinarith

theorem domination_count (G : SimpleGraph V) (label : V → ι)
    (I : Finset V) (n d : ℕ)
    (hparts : ∀ i, (fiber label i).card = n)
    (hdegree : ∀ v, degree G v ≤ d)
    (hdom : ∀ v, label v ∈ I.image label → ∃ w ∈ I, G.Adj w v) :
    (I.image label).card * n ≤ I.card * d := by
  have hsize : (activeVertices label (I.image label)).card =
      (I.image label).card * n := by
    rw [← sum_fiber_card]
    simp only [hparts, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  have h₁ := dominated_card_le_sum_degree G (activeVertices label (I.image label)) I
    (fun v hv => hdom v ((mem_activeVertices _ _ _).mp hv))
  have h₂ : (∑ w ∈ I, degree G w) ≤ I.card * d := by
    calc
      (∑ w ∈ I, degree G w) ≤ ∑ _w ∈ I, d := Finset.sum_le_sum fun w _ => hdegree w
      _ = I.card * d := by simp
  rw [hsize] at h₁
  exact h₁.trans h₂

theorem Feasible.full_active_of_degree {G : SimpleGraph V} {label : V → ι}
    {I T : Finset V} (hF : Feasible G label I T) (hI : I.Nonempty)
    (hpart : ∀ ⦃v w⦄, G.Adj v w → label v ≠ label w)
    (n d : ℕ) (hr : 3 ≤ Fintype.card ι)
    (hparts : ∀ i, (fiber label i).card = n)
    (hdegree : ∀ v, degree G v ≤ d)
    (hdeg : (2 * (Fintype.card ι : ℝ) - 4) * d < ((Fintype.card ι : ℝ) - 1) * n)
    (hdom : ∀ v, label v ∈ I.image label → ∃ w ∈ I, G.Adj w v) :
    I.image label = Finset.univ := by
  classical
  have hq := hF.two_le_active_card hI hpart
  have hsize := hF.card_le_twice_active_sub_one hI hpart
  have hcount := domination_count G label I n d hparts hdegree hdom
  have hqle : (I.image label).card ≤ Fintype.card ι := Finset.card_le_univ _
  have heq : (I.image label).card = Fintype.card ι := by
    by_contra hne
    have hlt : (I.image label).card + 1 ≤ Fintype.card ι := by omega
    have hcount' : ((I.image label).card : ℝ) * n ≤ (I.card : ℝ) * d := by
      exact_mod_cast hcount
    have hsize' : (I.card : ℝ) ≤ 2 * ((I.image label).card - 1 : ℕ) := by
      exact_mod_cast hsize
    have hsub : (((I.image label).card - 1 : ℕ) : ℝ) =
        ((I.image label).card : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [hsub] at hsize'
    have hreal : ((I.image label).card : ℝ) * n ≤
        2 * (((I.image label).card : ℝ) - 1) * d :=
      hcount'.trans (mul_le_mul_of_nonneg_right hsize' (Nat.cast_nonneg d))
    have hlt' : ((I.image label).card : ℝ) + 1 ≤ (Fintype.card ι : ℝ) := by
      exact_mod_cast hlt
    exact smaller_active_set_impossible (by exact_mod_cast (show 0 < (I.image label).card by omega))
      (by exact_mod_cast hr) (by linarith) (Nat.cast_nonneg d) hreal hdeg
  exact Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simpa using heq.ge)

theorem Feasible.matched_of_degree {G : SimpleGraph V} {label : V → ι}
    {I T : Finset V} (hF : Feasible G label I T) (hno : ¬ HasFull G label)
    (n d : ℕ) (hr : 3 ≤ Fintype.card ι)
    (hparts : ∀ i, (fiber label i).card = n)
    (hdegree : ∀ v, degree G v ≤ d)
    (hdeg : (2 * (Fintype.card ι : ℝ) - 4) * d < ((Fintype.card ι : ℝ) - 1) * n)
    (hall : I.image label = Finset.univ)
    (hdom : ∀ v, label v ∈ I.image label → ∃ w ∈ I, G.Adj w v) :
    ∀ v ∈ I, ∃! w, w ∈ I ∧ G.Adj v w := by
  rcases hF.matching_or_small hno with h | hsmall
  · exact h
  · have hcount := domination_count G label I n d hparts hdegree hdom
    rw [hall, Finset.card_univ] at hcount
    have hc : (Fintype.card ι : ℝ) * n ≤ (I.card : ℝ) * d := by exact_mod_cast hcount
    have hs : (I.card : ℝ) + 3 ≤ 2 * (Fintype.card ι : ℝ) := by exact_mod_cast hsmall
    have hm := matching_budget (by exact_mod_cast hr) (Nat.cast_nonneg d) hdeg
    have hmul := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg d)
    exact False.elim (by nlinarith)

theorem exists_matching_configuration (G : SimpleGraph V) (label : V → ι)
    (n d : ℕ) (hr : 3 ≤ Fintype.card ι) (hn : 0 < n)
    (hpart : ∀ ⦃v w⦄, G.Adj v w → label v ≠ label w)
    (hparts : ∀ i, (fiber label i).card = n)
    (hdegree : ∀ v, degree G v ≤ d)
    (hdeg : (2 * (Fintype.card ι : ℝ) - 4) * d < ((Fintype.card ι : ℝ) - 1) * n)
    (hno : ¬ HasFull G label) :
    ∃ I, MatchingConfiguration.Tree G label I Finset.univ ∧
      I.Nonempty ∧ ∀ v, ∃ w ∈ I, G.Adj w v := by
  classical
  have hsurj : ∀ i, ∃ v, label v = i := by
    intro i
    have hpos : 0 < (fiber label i).card := by rw [hparts]; exact hn
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    exact ⟨v, (mem_fiber _ _ _).mp hv⟩
  obtain ⟨I, T, hF, hI, hdom⟩ := exists_feasible_dominating G label hpart hsurj hno
  have hall := hF.full_active_of_degree hI hpart n d hr hparts hdegree hdeg hdom
  have hmatch := hF.matched_of_degree hno n d hr hparts hdegree hdeg hall hdom
  refine ⟨I, hF.toMatchingTree hpart hall hmatch, hI, ?_⟩
  intro v
  apply hdom
  simp only [hall, Finset.mem_univ]

end JSP896.FeasiblePair
