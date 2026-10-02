import JSP896.CertificateIMC
import JSP896.Statement
import Mathlib.Tactic

/-!
# Ordinary domination bound and literal balanced-graph adapters

This is the even-part sufficiency argument, proved from the finite feasible-pair
certificate. The certificate is constructed under a contradiction assumption;
its existence is not an additional hypothesis of the exported theorem.

Pinned compilation and audit records are in VERIFICATION.md.
-/

namespace JSP896

open FiniteTransversal

theorem hasFull_iff_independentTransversal {r n : ℕ}
    (G : SimpleGraph (Vertex r n)) :
    HasFull G Prod.fst ↔ HasIndependentTransversal G := by
  classical
  constructor
  · rintro ⟨T, hT⟩
    have hex : ∀ i : Fin r, ∃ v : Vertex r n, v ∈ T ∧ v.1 = i := by
      intro i
      have hi : i ∈ T.image Prod.fst := by rw [hT.2]; exact Finset.mem_univ i
      exact Finset.mem_image.mp hi
    choose v hv hcolor using hex
    refine ⟨fun i => (v i).2, ?_⟩
    intro i j _
    have heqi : v i = (i, (v i).2) := by
      apply Prod.ext
      · exact hcolor i
      · rfl
    have heqj : v j = (j, (v j).2) := by
      apply Prod.ext
      · exact hcolor j
      · rfl
    simpa only [← heqi, ← heqj] using hT.1.1 (v i) (hv i) (v j) (hv j)
  · rintro ⟨f, hf⟩
    let T : Finset (Vertex r n) := Finset.univ.image fun i => (i, f i)
    refine ⟨T, ⟨?_, ?_⟩, ?_⟩
    · intro x hx y hy hxy
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
      by_cases hij : i = j
      · subst j
        exact G.loopless.irrefl _ hxy
      · exact hf i j hij hxy
    · intro x hx y hy hcolor
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
      change i = j at hcolor
      subst j
      rfl
    · ext i
      constructor
      · intro _; exact Finset.mem_univ i
      · intro _
        exact Finset.mem_image.mpr ⟨(i, f i),
          Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, rfl⟩

@[simp] theorem balanced_fiber_card (r n : ℕ) (i : Fin r) :
    (FiniteGraphCounting.fiber (Prod.fst : Vertex r n → Fin r) i).card = n := by
  classical
  have hfiber : FiniteGraphCounting.fiber (Prod.fst : Vertex r n → Fin r) i =
      Finset.univ.image (fun j : Fin n => (i, j)) := by
    ext v
    simp only [FiniteGraphCounting.mem_fiber, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · intro h
      exact ⟨v.2, by apply Prod.ext <;> simp [h]⟩
    · rintro ⟨j, rfl⟩
      rfl
  have hinj : Function.Injective (fun j : Fin n => (i, j)) := by
    intro j k h
    exact congrArg Prod.snd h
  rw [hfiber, Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Fintype.card_fin]

@[simp] theorem generic_degree_eq {r n : ℕ}
    (G : SimpleGraph (Vertex r n)) (v : Vertex r n) :
    FiniteGraphCounting.degree G v = degree G v := rfl

namespace DominationSufficiency

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]

/-- The finite domination criterion, including every smaller active class set. -/
theorem hasFull_of_degree (G : SimpleGraph V) (label : V → ι)
    (n d : ℕ) (hr : 2 ≤ Fintype.card ι) (hn : 0 < n)
    (hpart : ∀ ⦃v w⦄, G.Adj v w → label v ≠ label w)
    (hparts : ∀ i, (FiniteGraphCounting.fiber label i).card = n)
    (hdegree : ∀ v, FiniteGraphCounting.degree G v ≤ d)
    (hdeg : (2 * (Fintype.card ι : ℝ) - 2) * d < (Fintype.card ι : ℝ) * n) :
    HasFull G label := by
  classical
  by_contra hno
  have hsurj : ∀ i, ∃ v, label v = i := by
    intro i
    have hpos : 0 < (FiniteGraphCounting.fiber label i).card := by rw [hparts]; exact hn
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    exact ⟨v, (FiniteGraphCounting.mem_fiber _ _ _).mp hv⟩
  obtain ⟨I, T, hF, hI, hdom⟩ :=
    FeasiblePair.exists_feasible_dominating G label hpart hsurj hno
  have hq := hF.two_le_active_card hI hpart
  have hsize := hF.card_le_twice_active_sub_one hI hpart
  have hcount := FeasiblePair.domination_count G label I n d hparts hdegree hdom
  have hqle : (I.image label).card ≤ Fintype.card ι := Finset.card_le_univ _
  have hcount' : ((I.image label).card : ℝ) * n ≤ (I.card : ℝ) * d := by
    exact_mod_cast hcount
  have hsize' : (I.card : ℝ) ≤ 2 * ((I.image label).card - 1 : ℕ) := by
    exact_mod_cast hsize
  have hsub : (((I.image label).card - 1 : ℕ) : ℝ) =
      ((I.image label).card : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [hsub] at hsize'
  have hdom' : ((I.image label).card : ℝ) * n ≤
      2 * (((I.image label).card : ℝ) - 1) * d :=
    hcount'.trans (mul_le_mul_of_nonneg_right hsize' (Nat.cast_nonneg d))
  have hqpos : (0 : ℝ) < (I.image label).card := by exact_mod_cast (show 0 < (I.image label).card by omega)
  have hrpos : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hqle' : ((I.image label).card : ℝ) ≤ Fintype.card ι := by exact_mod_cast hqle
  have hleft := mul_le_mul_of_nonneg_left hdom' hrpos
  have hright := mul_lt_mul_of_pos_left hdeg hqpos
  have hgap : 0 ≤ 2 * ((Fintype.card ι : ℝ) - (I.image label).card) * d :=
    mul_nonneg (by linarith) (Nat.cast_nonneg d)
  nlinarith

end DominationSufficiency

/-- Literal balanced-graph form of the ordinary (even-case) bound. -/
theorem independentTransversal_of_even_bound {r n : ℕ}
    (G : SimpleGraph (Vertex r n)) (d : ℕ) (hr : 2 ≤ r) (hn : 0 < n)
    (hpart : IsPartite G) (hdegree : ∀ v, degree G v ≤ d)
    (hdeg : (2 * (r : ℝ) - 2) * d < (r : ℝ) * n) :
    HasIndependentTransversal G := by
  apply (hasFull_iff_independentTransversal G).mp
  apply DominationSufficiency.hasFull_of_degree G Prod.fst n d
    (by simpa using hr) hn hpart
  · exact balanced_fiber_card r n
  · simpa only [generic_degree_eq] using hdegree
  · simpa only [Fintype.card_fin] using hdeg

end JSP896
