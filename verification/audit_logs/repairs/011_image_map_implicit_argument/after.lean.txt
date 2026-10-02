import JSP896.FeasibleExtension

/-! Finite maximal feasible extensions produce actual domination certificates.
No termination oracle or independent-transversal theorem is assumed. -/

namespace JSP896.FeasiblePair

open FiniteTransversal

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]

def ExtendsSeed (label : V → ι) (I₀ T₀ I T : Finset V) : Prop :=
  I₀ ⊆ I ∧ ∀ v, label v ∈ I₀.image label → (v ∈ T ↔ v ∈ T₀)

theorem extendsSeed_self (label : V → ι) (I T : Finset V) :
    ExtendsSeed label I T I T := ⟨Finset.Subset.refl _, fun _ _ => Iff.rfl⟩

theorem extendsSeed_compatible {G : SimpleGraph V} {label : V → ι}
    {I₀ T₀ I T I' U : Finset V} (hF : Feasible G label I T)
    (hseed : ExtendsSeed label I₀ T₀ I T) (hII' : I ⊆ I')
    (hU : Compatible G label I T U) : ExtendsSeed label I₀ T₀ I' U := by
  refine ⟨hseed.1.trans hII', ?_⟩
  intro v hv
  have hvI : label v ∈ I.image label := Finset.image_subset_image (f := label) hseed.1 hv
  have hsame : v ∈ U ↔ v ∈ T := by
    constructor
    · intro h
      exact compatible_vertex_on_active_mem_T hF hU h hvI
    · intro h
      exact active_T_vertex_mem_compatible hF hU h hvI
  exact hsame.trans (hseed.2 v hv)

theorem exists_dominating_extension (G : SimpleGraph V) (label : V → ι)
    (hpart : ∀ ⦃x y⦄, G.Adj x y → label x ≠ label y)
    (hsurj : ∀ i, ∃ v, label v = i) (hno : ¬ HasFull G label)
    (I₀ T₀ : Finset V) (hF₀ : Feasible G label I₀ T₀) :
    ∃ I T, Feasible G label I T ∧ ExtendsSeed label I₀ T₀ I T ∧
      I.Nonempty ∧ ∀ v, label v ∈ I.image label → ∃ w ∈ I, G.Adj w v := by
  classical
  let allSets := (Finset.univ : Finset V).powerset
  let candidates := (allSets.product allSets).filter fun P : Finset V × Finset V =>
    Feasible G label P.1 P.2 ∧ ExtendsSeed label I₀ T₀ P.1 P.2
  have hmem (I T : Finset V) (hF : Feasible G label I T)
      (hseed : ExtendsSeed label I₀ T₀ I T) : (I, T) ∈ candidates := by
    simp [candidates, allSets, hF, hseed]
  have hne : candidates.Nonempty :=
    ⟨(I₀, T₀), hmem I₀ T₀ hF₀ (extendsSeed_self label I₀ T₀)⟩
  obtain ⟨P, hP, hmax⟩ := candidates.exists_max_image (fun P => P.1.card) hne
  let I := P.1
  let T := P.2
  have hF : Feasible G label I T := (Finset.mem_filter.mp hP).2.1
  have hseed : ExtendsSeed label I₀ T₀ I T := (Finset.mem_filter.mp hP).2.2
  have hcannot (c : V) (havoid : ∀ v ∈ I, ¬ G.Adj c v)
      (hclass : label c ∈ I.image label ∨ label c ∉ T.image label)
      (hwhere : I = ∅ ∨ label c ∈ I.image label) : False := by
    obtain ⟨I', T', hF', hsub, hlt, hCompat⟩ :=
      exists_feasible_extension hF hpart c havoid hclass hwhere
    have hseed' := extendsSeed_compatible hF hseed hsub hCompat
    have hle := hmax (I', T') (hmem I' T' hF' hseed')
    change I'.card ≤ I.card at hle
    omega
  have hI : I.Nonempty := by
    by_contra h
    have hEmpty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hmissing : ∃ i, i ∉ T.image label := by
      by_contra hmissing
      have hall : ∀ i, i ∈ T.image label := by
        intro i
        by_contra hi
        exact hmissing ⟨i, hi⟩
      exact hno ⟨T, hF.maximum.1, Finset.eq_univ_iff_forall.mpr hall⟩
    obtain ⟨i, hi⟩ := hmissing
    obtain ⟨c, hci⟩ := hsurj i
    have havoid : ∀ v ∈ I, ¬ G.Adj c v := by simp [hEmpty]
    have hc : label c ∉ T.image label := by simpa only [hci] using hi
    exact hcannot c havoid (Or.inr hc) (Or.inl hEmpty)
  refine ⟨I, T, hF, hseed, hI, ?_⟩
  intro v hv
  by_contra h
  have havoid : ∀ w ∈ I, ¬ G.Adj v w := by
    intro w hw hvw
    exact h ⟨w, hw, G.adj_symm hvw⟩
  exact hcannot v havoid (Or.inl hv) (Or.inr hv)

theorem exists_feasible_dominating (G : SimpleGraph V) (label : V → ι)
    (hpart : ∀ ⦃x y⦄, G.Adj x y → label x ≠ label y)
    (hsurj : ∀ i, ∃ v, label v = i) (hno : ¬ HasFull G label) :
    ∃ I T, Feasible G label I T ∧ I.Nonempty ∧
      ∀ v, label v ∈ I.image label → ∃ w ∈ I, G.Adj w v := by
  obtain ⟨T₀, hT₀⟩ := exists_maximum G label
  obtain ⟨I, T, hF, _, hI, hdom⟩ :=
    exists_dominating_extension G label hpart hsurj hno ∅ T₀
      (feasible_empty G label T₀ hT₀)
  exact ⟨I, T, hF, hI, hdom⟩

theorem Feasible.two_le_active_card {G : SimpleGraph V} {label : V → ι}
    {I T : Finset V} (hF : Feasible G label I T) (hI : I.Nonempty)
    (hpart : ∀ ⦃x y⦄, G.Adj x y → label x ≠ label y) :
    2 ≤ (I.image label).card := by
  classical
  obtain ⟨v, hv⟩ := hI
  obtain ⟨w, hw, hvw⟩ := hF.nonisolated v hv
  have hne := hpart hvw
  have hsub : ({label v, label w} : Finset ι) ⊆ I.image label := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    · have hiw := Finset.mem_singleton.mp hi
      subst i
      exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
  have hcard := Finset.card_le_card hsub
  simpa [hne] using hcard

end JSP896.FeasiblePair
