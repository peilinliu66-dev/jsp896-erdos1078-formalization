import JSP896.CellDeletion

/-! Coverage and the simultaneous asymmetric completion of opposite cells. -/

namespace JSP896.MatchingConfiguration

open FiniteTransversal FiniteGraphCounting
open scoped BigOperators

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]

def CompleteTo (G : SimpleGraph V) (v : V) (A : Finset V) : Prop :=
  ∀ w ∈ A, G.Adj v w

theorem deficit_subset_lt {κ : Type*} [Fintype κ] [DecidableEq κ]
    (δ : κ → ℝ) (d : ℝ) (hδ : ∀ i, 0 ≤ δ i) (hdef : (∑ i, δ i) < d)
    (S : Finset κ) : (∑ i ∈ S, δ i) < d := by
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun i _ _ => hδ i)).trans_lt hdef

theorem Tree.complete_to_some_cell {G : SimpleGraph V} {label : V → ι} {I : Finset V}
    (M : Tree G label I Finset.univ) (hno : ¬ HasFull G label)
    (d : ℕ) (hdegree : ∀ v, degree G v ≤ d)
    (hdef : (∑ i : IVertex I, ((d : ℝ) - (cell G I i).card)) < d) (v : V) :
    ∃ i : IVertex I, CompleteTo G v (cell G I i) := by
  classical
  by_contra h
  let R (i : IVertex I) := (cell G I i).filter (G.Adj v)
  have hR (i : IVertex I) : R i ⊆ cell G I i := Finset.filter_subset _ _
  have hremove : (∑ i, (R i).card) ≤ d := by
    apply (disjoint_family_sum_le R (fun i j hij =>
      (cells_disjoint G I hij).mono (hR i) (hR j)) (neighbors G v) ?_).trans (hdegree v)
    intro i w hw
    exact (mem_neighbors G v w).mpr (Finset.mem_filter.mp hw).2
  have hne (i : IVertex I) : (cell G I i \ R i).Nonempty := by
    have hn : ¬ CompleteTo G v (cell G I i) := fun hi => h ⟨i, hi⟩
    change ¬ (∀ w ∈ cell G I i, G.Adj v w) at hn
    push_neg at hn
    obtain ⟨w, hw, hvw⟩ := hn
    exact ⟨w, Finset.mem_sdiff.mpr ⟨hw, by simpa [R, hw] using hvw⟩⟩
  obtain ⟨f, hf, N, hadj⟩ := M.imc_after_deletion hno R d hdegree hdef hR hremove hne
  obtain ⟨w, hw, hwv⟩ := N.dominates hno v
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
  have hnot := (Finset.mem_sdiff.mp (hf i)).2
  exact hnot (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp (hf i)).1, G.adj_symm hwv⟩)

theorem Tree.complete_cell_unique {G : SimpleGraph V} {label : V → ι} {I : Finset V}
    (M : Tree G label I Finset.univ) (d : ℕ) (hdegree : ∀ v, degree G v ≤ d)
    (hdef : (∑ i : IVertex I, ((d : ℝ) - (cell G I i).card)) < d)
    (v : V) {i j : IVertex I}
    (hi : CompleteTo G v (cell G I i)) (hj : CompleteTo G v (cell G I j)) : i = j := by
  classical
  by_contra hij
  have hδ (k : IVertex I) : 0 ≤ (d : ℝ) - (cell G I k).card := by
    have h : ((cell G I k).card : ℝ) ≤ d := by
      exact_mod_cast (cell_card_le_degree G I k).trans (hdegree k.1)
    linarith
  have hsum := deficit_subset_lt _ (d : ℝ) hδ hdef {i, j}
  have hs : ((d : ℝ) - (cell G I i).card) +
      (d - (cell G I j).card) < d := by
    simpa only [Finset.sum_pair hij] using hsum
  have hsub : cell G I i ∪ cell G I j ⊆ neighbors G v := by
    intro w hw
    exact (mem_neighbors G v w).mpr ((Finset.mem_union.mp hw).elim (hi w) (hj w))
  have hnat := (Finset.card_le_card hsub).trans (hdegree v)
  rw [Finset.card_union_of_disjoint (cells_disjoint G I hij)] at hnat
  have hr : ((cell G I i).card : ℝ) + (cell G I j).card ≤ d := by exact_mod_cast hnat
  linarith

/-- Opposite completeness for arbitrary vertices complete to old cells. All
deletions are made in the old cells at once, including the distinguished pair. -/
theorem Tree.expanded_opposite_complete {G : SimpleGraph V} {label : V → ι} {I : Finset V}
    (M : Tree G label I Finset.univ) (hno : ¬ HasFull G label)
    (d : ℕ) (hdegree : ∀ v, degree G v ≤ d)
    (hdef : (∑ i : IVertex I, ((d : ℝ) - (cell G I i).card)) < d)
    (i : IVertex I) (a b : V)
    (ha : CompleteTo G a (cell G I (M.partner i)))
    (hb : CompleteTo G b (cell G I i)) : G.Adj a b := by
  classical
  let C := cell G I
  let δ : IVertex I → ℝ := fun j => d - (C j).card
  have hδ (j : IVertex I) : 0 ≤ δ j := by
    have h : ((C j).card : ℝ) ≤ d := by
      exact_mod_cast (cell_card_le_degree G I j).trans (hdegree j.1)
    dsimp [δ]
    linarith
  have hpair : δ i + δ (M.partner i) < d := by
    have h := deficit_subset_lt δ d hδ hdef {i, M.partner i}
    simpa only [Finset.sum_pair (Ne.symm (M.partner_ne i))] using h
  have hthree (j : IVertex I) (hji : j ≠ i) (hjp : j ≠ M.partner i) :
      δ j + δ i + δ (M.partner i) < d := by
    have h := deficit_subset_lt δ d hδ hdef {j, i, M.partner i}
    have hnot : j ∉ ({i, M.partner i} : Finset (IVertex I)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact not_or_intro hji hjp
    simpa only [Finset.sum_insert hnot,
      Finset.sum_pair (Ne.symm (M.partner_ne i)), add_assoc] using h
  have hCa : C (M.partner i) ⊆ neighbors G a := fun v hv => (mem_neighbors G a v).mpr (ha v hv)
  have hCb : C i ⊆ neighbors G b := fun v hv => (mem_neighbors G b v).mpr (hb v hv)
  let U := (neighbors G a \ C (M.partner i)) ∪ (neighbors G b \ C i)
  let R (j : IVertex I) := C j ∩ U
  have hR (j : IVertex I) : R j ⊆ C j := Finset.inter_subset_left
  have hUa : ((neighbors G a \ C (M.partner i)).card : ℝ) ≤ δ (M.partner i) := by
    have he := Finset.card_sdiff_add_card_eq_card hCa
    have he' : ((neighbors G a \ C (M.partner i)).card : ℝ) + (C (M.partner i)).card =
        degree G a := by exact_mod_cast he
    have hd : (degree G a : ℝ) ≤ d := by exact_mod_cast hdegree a
    dsimp [δ]
    linarith
  have hUb : ((neighbors G b \ C i).card : ℝ) ≤ δ i := by
    have he := Finset.card_sdiff_add_card_eq_card hCb
    have he' : ((neighbors G b \ C i).card : ℝ) + (C i).card = degree G b := by
      exact_mod_cast he
    have hd : (degree G b : ℝ) ≤ d := by exact_mod_cast hdegree b
    dsimp [δ]
    linarith
  have hU : (U.card : ℝ) ≤ δ i + δ (M.partner i) := by
    have h := Finset.card_union_le (neighbors G a \ C (M.partner i)) (neighbors G b \ C i)
    have h' : (U.card : ℝ) ≤ (neighbors G a \ C (M.partner i)).card +
        (neighbors G b \ C i).card := by exact_mod_cast h
    linarith
  have hremove : (∑ j, (R j).card) ≤ d := by
    have hn := disjoint_family_sum_le R (fun j k hjk =>
      (cells_disjoint G I hjk).mono (hR j) (hR k)) U (fun _ => Finset.inter_subset_right)
    have hr : ((∑ j, (R j).card) : ℝ) ≤ U.card := by exact_mod_cast hn
    have hd : ((∑ j, (R j).card) : ℝ) < d := (hr.trans hU).trans_lt hpair
    exact_mod_cast hd.le
  have hne (j : IVertex I) : (C j \ R j).Nonempty := by
    have hRlt : (R j).card < (C j).card := by
      by_cases hji : j = i
      · subst j
        have hsub : R i ⊆ neighbors G a \ C (M.partner i) := by
          intro v hv
          obtain ⟨hvC, hvU⟩ := Finset.mem_inter.mp hv
          rcases Finset.mem_union.mp hvU with h | h
          · exact h
          · exact False.elim ((Finset.mem_sdiff.mp h).2 hvC)
        have hr : ((R i).card : ℝ) ≤ (neighbors G a \ C (M.partner i)).card := by
          exact_mod_cast Finset.card_le_card hsub
        have hc : ((R i).card : ℝ) < (C i).card := by
          dsimp [δ] at hpair hUa
          linarith
        exact_mod_cast hc
      · by_cases hjp : j = M.partner i
        · subst j
          have hsub : R (M.partner i) ⊆ neighbors G b \ C i := by
            intro v hv
            obtain ⟨hvC, hvU⟩ := Finset.mem_inter.mp hv
            rcases Finset.mem_union.mp hvU with h | h
            · exact False.elim ((Finset.mem_sdiff.mp h).2 hvC)
            · exact h
          have hr : ((R (M.partner i)).card : ℝ) ≤ (neighbors G b \ C i).card := by
            exact_mod_cast Finset.card_le_card hsub
          have hc : ((R (M.partner i)).card : ℝ) < (C (M.partner i)).card := by
            dsimp [δ] at hpair hUb
            linarith
          exact_mod_cast hc
        · have hr : ((R j).card : ℝ) ≤ U.card := by
            exact_mod_cast Finset.card_le_card (show R j ⊆ U from Finset.inter_subset_right)
          have ht := hthree j hji hjp
          have hc : ((R j).card : ℝ) < (C j).card := by
            dsimp [δ] at ht hU
            linarith
          exact_mod_cast hc
    apply Finset.card_pos.mp
    rw [Finset.card_sdiff_of_subset (hR j)]
    omega
  obtain ⟨f, hf, N, hfedge⟩ := M.imc_after_deletion hno R d hdegree hdef hR hremove hne
  have hfinj : Function.Injective f := by
    intro j k he
    by_contra hjk
    exact Finset.disjoint_left.mp (cells_disjoint G I hjk)
      (Finset.mem_sdiff.mp (hf j)).1 (he.symm ▸ (Finset.mem_sdiff.mp (hf k)).1)
  have haf (j : IVertex I) : G.Adj a (f j) ↔ j = M.partner i := by
    constructor
    · intro hadj
      by_contra hj
      have hfc := (Finset.mem_sdiff.mp (hf j)).1
      have hfnot := (Finset.mem_sdiff.mp (hf j)).2
      have hnot : f j ∉ C (M.partner i) := fun h =>
        Finset.disjoint_left.mp (cells_disjoint G I hj) hfc h
      apply hfnot
      exact Finset.mem_inter.mpr ⟨hfc, Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨(mem_neighbors G a _).mpr hadj, hnot⟩)⟩
    · intro h
      subst j
      exact ha _ (Finset.mem_sdiff.mp (hf _)).1
  have hbf (j : IVertex I) : G.Adj b (f j) ↔ j = i := by
    constructor
    · intro hadj
      by_contra hj
      have hfc := (Finset.mem_sdiff.mp (hf j)).1
      have hfnot := (Finset.mem_sdiff.mp (hf j)).2
      have hnot : f j ∉ C i := fun h =>
        Finset.disjoint_left.mp (cells_disjoint G I hj) hfc h
      apply hfnot
      exact Finset.mem_inter.mpr ⟨hfc, Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨(mem_neighbors G b _).mpr hadj, hnot⟩)⟩
    · intro h
      subst j
      exact hb _ (Finset.mem_sdiff.mp (hf _)).1
  let u : IVertex (Finset.univ.image f) := ⟨f (M.partner i), Finset.mem_image.mpr
    ⟨M.partner i, Finset.mem_univ _, rfl⟩⟩
  let w : IVertex (Finset.univ.image f) := ⟨f i, Finset.mem_image.mpr
    ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hpartner : N.partner u = w := (N.adj_iff_partner u w).mp
    ((hfedge (M.partner i) i).mpr (M.partner_involutive i))
  have haNew : a ∈ cell G (Finset.univ.image f) u := by
    apply (mem_cell G _ u a).mpr
    intro z
    obtain ⟨j, hj, hjz⟩ := Finset.mem_image.mp z.2
    constructor
    · intro hadj
      have he := (haf j).mp (by simpa only [hjz] using hadj)
      apply Subtype.ext
      exact hjz.symm.trans (congrArg f he)
    · intro h
      subst z
      exact (haf _).mpr rfl
  have hbNew : b ∈ cell G (Finset.univ.image f) (N.partner u) := by
    rw [hpartner]
    apply (mem_cell G _ w b).mpr
    intro z
    obtain ⟨j, hj, hjz⟩ := Finset.mem_image.mp z.2
    constructor
    · intro hadj
      have he := (hbf j).mp (by simpa only [hjz] using hadj)
      apply Subtype.ext
      exact hjz.symm.trans (congrArg f he)
    · intro h
      subst z
      exact (hbf _).mpr rfl
  exact N.opposite_cells_complete hno u haNew hbNew

structure ExpandedPartition {G : SimpleGraph V} {label : V → ι} {I : Finset V}
    (M : Tree G label I Finset.univ) where
  index : V → IVertex I
  core_index : ∀ i, ∀ v ∈ cell G I i, index v = i
  complete : ∀ v, CompleteTo G v (cell G I (M.partner (index v)))
  opposite_complete : ∀ v w, M.partner (index v) = index w → G.Adj v w

theorem Tree.exists_expanded_partition {G : SimpleGraph V} {label : V → ι} {I : Finset V}
    (M : Tree G label I Finset.univ) (hno : ¬ HasFull G label)
    (d : ℕ) (hdegree : ∀ v, degree G v ≤ d)
    (hdef : (∑ i : IVertex I, ((d : ℝ) - (cell G I i).card)) < d) :
    Nonempty (ExpandedPartition M) := by
  classical
  have hex := M.complete_to_some_cell hno d hdegree hdef
  let target : V → IVertex I := fun v => Classical.choose (hex v)
  have ht (v : V) : CompleteTo G v (cell G I (target v)) := Classical.choose_spec (hex v)
  let index (v : V) := M.partner (target v)
  have hcomplete (v : V) : CompleteTo G v (cell G I (M.partner (index v))) := by
    simpa only [index, M.partner_involutive] using ht v
  refine ⟨⟨index, ?_, hcomplete, ?_⟩⟩
  · intro i v hv
    have h : target v = M.partner i := M.complete_cell_unique d hdegree hdef v (ht v)
      (fun w hw => M.opposite_cells_complete hno i hv hw)
    simp only [index, h, M.partner_involutive]
  · intro v w hvw
    apply M.expanded_opposite_complete hno d hdegree hdef (index v) v w (hcomplete v)
    simpa only [← hvw, M.partner_involutive] using hcomplete w

end JSP896.MatchingConfiguration
