import JSP896.MatchingExchange

/-! Incidence counts for the actual unique-neighbour cells. -/

namespace JSP896.MatchingConfiguration

open FiniteTransversal FiniteGraphCounting
open scoped BigOperators

variable {V ι κ : Type*} [Fintype V] [Fintype ι] [Fintype κ]
  [DecidableEq V] [DecidableEq ι] [DecidableEq κ]

theorem disjoint_family_card (C : κ → Finset V)
    (hdis : ∀ i j, i ≠ j → Disjoint (C i) (C j)) :
    (Finset.univ.biUnion C).card = ∑ i, (C i).card := by
  classical
  have h (S : Finset κ) : (S.biUnion C).card = ∑ i ∈ S, (C i).card := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      have hd : Disjoint (C i) (S.biUnion C) := by
        apply Finset.disjoint_left.mpr
        intro v hvi hvS
        obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.mp hvS
        exact Finset.disjoint_left.mp (hdis i j (fun h => hi (h.symm ▸ hj))) hvi hvj
      rw [Finset.biUnion_insert, Finset.card_union_of_disjoint hd, ih, Finset.sum_insert hi]
  exact h Finset.univ

theorem disjoint_family_sum_le (C : κ → Finset V)
    (hdis : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (B : Finset V) (hsub : ∀ i, C i ⊆ B) : (∑ i, (C i).card) ≤ B.card := by
  rw [← disjoint_family_card C hdis]
  apply Finset.card_le_card
  intro v hv
  obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
  exact hsub i hvi

noncomputable def core (G : SimpleGraph V) (I : Finset V) : Finset V := by
  classical
  exact Finset.univ.biUnion (cell G I)

@[simp] theorem mem_core (G : SimpleGraph V) (I : Finset V) (v : V) :
    v ∈ core G I ↔ ∃ i : IVertex I, v ∈ cell G I i := by
  classical
  simp [core]

theorem core_card (G : SimpleGraph V) (I : Finset V) :
    (core G I).card = ∑ i : IVertex I, (cell G I i).card :=
  disjoint_family_card _ (fun _ _ h => cells_disjoint G I h)

noncomputable def matchingNeighbors (G : SimpleGraph V) (I : Finset V) (v : V) :
    Finset (IVertex I) := by
  classical
  exact Finset.univ.filter fun i => G.Adj v i.1

@[simp] theorem mem_matchingNeighbors (G : SimpleGraph V) (I : Finset V) (v : V)
    (i : IVertex I) : i ∈ matchingNeighbors G I v ↔ G.Adj v i.1 := by
  classical
  simp [matchingNeighbors]

theorem mem_core_iff_one (G : SimpleGraph V) (I : Finset V) (v : V) :
    v ∈ core G I ↔ (matchingNeighbors G I v).card = 1 := by
  classical
  rw [mem_core, Finset.card_eq_one]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    ext j
    simp only [mem_matchingNeighbors, Finset.mem_singleton]
    exact (mem_cell G I i v).mp hi j
  · rintro ⟨i, hi⟩
    refine ⟨i, (mem_cell G I i v).mpr ?_⟩
    intro j
    rw [← mem_matchingNeighbors, hi, Finset.mem_singleton]

theorem incidence_sum (G : SimpleGraph V) (I : Finset V) :
    (∑ v, (matchingNeighbors G I v).card) =
      ∑ i : IVertex I, degree G i.1 := by
  classical
  simp only [matchingNeighbors, degree, neighbors, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro v hv
  congr 1
  exact propext ⟨G.adj_symm, G.adj_symm⟩

theorem core_mass_bound (G : SimpleGraph V) (I : Finset V) (d : ℕ)
    (hdegree : ∀ v, degree G v ≤ d)
    (hdom : ∀ v, ∃ w ∈ I, G.Adj w v) :
    2 * Fintype.card V ≤ (core G I).card + I.card * d := by
  classical
  have hpoint (v : V) : 2 ≤ (if v ∈ core G I then 1 else 0) +
      (matchingNeighbors G I v).card := by
    obtain ⟨w, hw, hwv⟩ := hdom v
    have hp : 0 < (matchingNeighbors G I v).card := Finset.card_pos.mpr
      ⟨⟨w, hw⟩, (mem_matchingNeighbors G I v _).mpr (G.adj_symm hwv)⟩
    by_cases hv : v ∈ core G I
    · rw [if_pos hv, (mem_core_iff_one G I v).mp hv]
    · have hn := mt (mem_core_iff_one G I v).mpr hv
      rw [if_neg hv]
      omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hpoint v)
  have hcount : (∑ v : V, if v ∈ core G I then 1 else 0) = (core G I).card := by
    have heq : Finset.univ.filter (fun v : V => v ∈ core G I) = core G I := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [Finset.sum_boole, heq, Nat.cast_id]
  rw [Finset.sum_add_distrib, hcount, incidence_sum] at hs
  have hdeg : (∑ i : IVertex I, degree G i.1) ≤ I.card * d := by
    calc
      _ ≤ ∑ _i : IVertex I, d := Finset.sum_le_sum fun i _ => hdegree i.1
      _ = _ := by simp
  have hleft : (∑ _v : V, (2 : ℕ)) = 2 * Fintype.card V := by simp [Nat.mul_comm]
  rw [hleft] at hs
  omega

noncomputable def multiplyDominated (G : SimpleGraph V) (I : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => 2 ≤ (matchingNeighbors G I v).card

@[simp] theorem mem_multiplyDominated (G : SimpleGraph V) (I : Finset V) (v : V) :
    v ∈ multiplyDominated G I ↔ 2 ≤ (matchingNeighbors G I v).card := by
  classical
  simp [multiplyDominated]

theorem multiple_domination_bound (G : SimpleGraph V) (I : Finset V) (d : ℕ)
    (hdegree : ∀ v, degree G v ≤ d)
    (hdom : ∀ v, ∃ w ∈ I, G.Adj w v) :
    Fintype.card V + (multiplyDominated G I).card ≤ I.card * d := by
  classical
  have hpoint (v : V) : 1 + (if v ∈ multiplyDominated G I then 1 else 0) ≤
      (matchingNeighbors G I v).card := by
    obtain ⟨w, hw, hwv⟩ := hdom v
    have hp : 0 < (matchingNeighbors G I v).card := Finset.card_pos.mpr
      ⟨⟨w, hw⟩, (mem_matchingNeighbors G I v _).mpr (G.adj_symm hwv)⟩
    by_cases hv : v ∈ multiplyDominated G I
    · rw [if_pos hv]
      exact (mem_multiplyDominated G I v).mp hv
    · rw [if_neg hv]
      omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hpoint v)
  have hc : (∑ v : V, if v ∈ multiplyDominated G I then 1 else 0) =
      (multiplyDominated G I).card := by
    have heq : Finset.univ.filter (fun v : V => v ∈ multiplyDominated G I) = multiplyDominated G I := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [Finset.sum_boole, heq, Nat.cast_id]
  rw [Finset.sum_add_distrib, hc, incidence_sum] at hs
  have hd : (∑ i : IVertex I, degree G i.1) ≤ I.card * d := by
    calc
      _ ≤ ∑ _i : IVertex I, d := Finset.sum_le_sum fun i _ => hdegree i.1
      _ = _ := by simp
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
  exact hs.trans hd

theorem equal_parts_card (label : V → ι) (n : ℕ)
    (hparts : ∀ i, (fiber label i).card = n) :
    Fintype.card V = Fintype.card ι * n := by
  have h := sum_fiber_card label Finset.univ
  simpa only [hparts, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    activeVertices, Finset.mem_univ, Finset.filter_true, Nat.cast_id] using h.symm

theorem Tree.total_cell_deficit_lt {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} (M : Tree G label I Finset.univ) [Nonempty ι]
    (hno : ¬ HasFull G label) (n d : ℕ) (hr : 5 ≤ Fintype.card ι)
    (hparts : ∀ i, (fiber label i).card = n) (hdegree : ∀ v, degree G v ≤ d)
    (hdeg : (2 * (Fintype.card ι : ℝ) - 4) * d < ((Fintype.card ι : ℝ) - 1) * n) :
    (∑ i : IVertex I, ((d : ℝ) - (cell G I i).card)) < d := by
  have hb := JSP896.structure_budget (by exact_mod_cast hr) (Nat.cast_nonneg d) hdeg
  have hc := core_mass_bound G I d hdegree (M.dominates hno)
  have hnV := equal_parts_card label n hparts
  have hI := M.full_card
  have hc' : 2 * (Fintype.card V : ℝ) ≤ (core G I).card + (I.card : ℝ) * d := by
    exact_mod_cast hc
  have hI' : (I.card : ℝ) + 2 = 2 * (Fintype.card ι : ℝ) := by exact_mod_cast hI
  have hV' : (Fintype.card V : ℝ) = (Fintype.card ι : ℝ) * n := by exact_mod_cast hnV
  have hmass : ((core G I).card : ℝ) = ∑ i : IVertex I, ((cell G I i).card : ℝ) := by
    exact_mod_cast core_card G I
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    nsmul_eq_mul, ← hmass]
  have hIeq : (I.card : ℝ) = 2 * (Fintype.card ι : ℝ) - 2 := by linarith
  rw [hIeq] at hc' ⊢
  rw [hV'] at hc'
  nlinarith

end JSP896.MatchingConfiguration
