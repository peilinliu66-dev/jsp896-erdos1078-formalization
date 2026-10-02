import JSP896.ExpandedCells

/-!
# Uniform cell structure for r ≥ 5

Expanded cells are larger than the total multiple-domination budget. Therefore
every literal IMC uses exactly one vertex in each expanded cell. Critical-edge
containment then removes every extra edge and gives the literal
`BipartiteModel` interface used by component switching.
-/

namespace JSP896.MatchingConfiguration

open FiniteTransversal FiniteGraphCounting
open scoped BigOperators

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]

theorem ExpandedPartition.index_on_matching {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} {M : Tree G label I Finset.univ} (B : ExpandedPartition M)
    (i : IVertex I) : B.index i.1 = M.partner i := by
  apply B.core_index
  simpa only [M.partner_involutive] using M.partner_mem_cell (M.partner i)

theorem ExpandedPartition.fiber_nonempty {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} {M : Tree G label I Finset.univ} (B : ExpandedPartition M)
    (i : IVertex I) : (fiber B.index i).Nonempty := by
  refine ⟨(M.partner i).1, (mem_fiber B.index i _).mpr ?_⟩
  rw [B.index_on_matching, M.partner_involutive]

theorem ExpandedPartition.fiber_card_le {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} {M : Tree G label I Finset.univ} (B : ExpandedPartition M)
    (d : ℕ) (hdegree : ∀ v, degree G v ≤ d) (i : IVertex I) :
    (fiber B.index i).card ≤ d := by
  apply (Finset.card_le_card (show fiber B.index i ⊆ neighbors G i.1 from ?_)).trans (hdegree i.1)
  intro v hv
  apply (mem_neighbors G i.1 v).mpr
  apply B.opposite_complete
  rw [B.index_on_matching, M.partner_involutive, (mem_fiber B.index i v).mp hv]

theorem ExpandedPartition.fiber_mass_lower {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} {M : Tree G label I Finset.univ} (B : ExpandedPartition M)
    (d : ℕ) (hdegree : ∀ v, degree G v ≤ d) (i : IVertex I) :
    (Fintype.card V : ℝ) ≤ (fiber B.index i).card + ((I.card : ℝ) - 1) * d := by
  classical
  have hcardNat : (∑ j : IVertex I, (fiber B.index j).card) = Fintype.card V := by
    simpa [activeVertices] using sum_fiber_card B.index Finset.univ
  have hcard : (∑ j : IVertex I, ((fiber B.index j).card : ℝ)) = Fintype.card V := by
    exact_mod_cast hcardNat
  have hpoint (j : IVertex I) : ((fiber B.index j).card : ℝ) ≤
      if j = i then ((fiber B.index i).card : ℝ) else (d : ℝ) := by
    split_ifs with h
    · subst j; exact le_rfl
    · exact_mod_cast B.fiber_card_le d hdegree j
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hpoint j)
  rw [hcard] at hs
  have he : (∑ j : IVertex I, if j = i then ((fiber B.index i).card : ℝ) else d) =
      (I.card : ℝ) * d + (fiber B.index i).card - d := by
    calc
      _ = ∑ j : IVertex I, ((d : ℝ) + if j = i then ((fiber B.index i).card : ℝ) - (d : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        split_ifs <;> ring
      _ = _ := by simp [Finset.sum_add_distrib]; ring
  rw [he] at hs
  nlinarith

theorem ExpandedPartition.index_injective_on_imc {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} {M : Tree G label I Finset.univ} (B : ExpandedPartition M)
    [Nonempty ι] (hno : ¬ HasFull G label) (d : ℕ)
    (hdegree : ∀ v, degree G v ≤ d)
    (hbudget : (2 * (I.card : ℝ) - 1) * d < 2 * Fintype.card V)
    {J : Finset V} (N : Tree G label J Finset.univ) :
    Function.Injective (fun v : IVertex J => B.index v.1) := by
  classical
  intro x y hxy
  by_contra hne
  have hJcard : J.card = I.card := by
    have hI := M.full_card
    have hJ := N.full_card
    omega
  let i := M.partner (B.index x.1)
  have hsub : fiber B.index i ⊆ multiplyDominated G J := by
    intro v hv
    apply (mem_multiplyDominated G J v).mpr
    have hvindex : B.index v = i := (mem_fiber B.index i v).mp hv
    have hxv : G.Adj x.1 v := B.opposite_complete x.1 v hvindex.symm
    have hyv : G.Adj y.1 v := B.opposite_complete y.1 v (by simpa only [← hxy] using hvindex.symm)
    have hpair : ({x, y} : Finset (IVertex J)) ⊆ matchingNeighbors G J v := by
      intro z hz
      rcases Finset.mem_insert.mp hz with hzx | hz
      · subst z
        exact (mem_matchingNeighbors G J v x).mpr (G.adj_symm hxv)
      · have hz' := Finset.mem_singleton.mp hz
        subst z
        exact (mem_matchingNeighbors G J v y).mpr (G.adj_symm hyv)
    have h := Finset.card_le_card hpair
    simpa [hne] using h
  have hmult := multiple_domination_bound G J d hdegree (N.dominates hno)
  rw [hJcard] at hmult
  have hmult' : (Fintype.card V : ℝ) + (multiplyDominated G J).card ≤ (I.card : ℝ) * d := by
    exact_mod_cast hmult
  have hle : ((fiber B.index i).card : ℝ) ≤ (multiplyDominated G J).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hlower := B.fiber_mass_lower d hdegree i
  nlinarith

theorem ExpandedPartition.edge_in_imc_opposite {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} {M : Tree G label I Finset.univ} (B : ExpandedPartition M)
    [Nonempty ι] (hno : ¬ HasFull G label) (d : ℕ)
    (hdegree : ∀ v, degree G v ≤ d)
    (hbudget : (2 * (I.card : ℝ) - 1) * d < 2 * Fintype.card V)
    {J : Finset V} (N : Tree G label J Finset.univ)
    {v w : V} (hv : v ∈ J) (hw : w ∈ J) (hvw : G.Adj v w) :
    M.partner (B.index v) = B.index w := by
  classical
  let idx : IVertex J → IVertex I := fun x => B.index x.1
  have hinj : Function.Injective idx := B.index_injective_on_imc hno d hdegree hbudget N
  have hcard : Fintype.card (IVertex J) = Fintype.card (IVertex I) := by
    have hI := M.full_card
    have hJ := N.full_card
    simp only [Fintype.card_coe]
    omega
  have hsurj : Function.Surjective idx :=
    ((Fintype.bijective_iff_injective_and_card idx).mpr ⟨hinj, hcard⟩).2
  obtain ⟨z, hz⟩ := hsurj (M.partner (B.index v))
  have hvz : G.Adj v z.1 := B.opposite_complete v z.1 hz.symm
  have hzw : z.1 = w := (N.partner_unique ⟨v, hv⟩ z.2 hvz).trans
    (N.partner_unique ⟨v, hv⟩ hw hvw).symm
  simpa only [idx, hzw] using hz.symm

/-- Once every edge is placed in a literal IMC, the expanded partition is a
genuine disjoint complete-bipartite model of the whole graph. -/
noncomputable def ExpandedPartition.to_bipartiteModel {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} {M : Tree G label I Finset.univ} (B : ExpandedPartition M)
    [Nonempty ι] (hno : ¬ HasFull G label) (d : ℕ)
    (hdegree : ∀ v, degree G v ≤ d)
    (hbudget : (2 * (I.card : ℝ) - 1) * d < 2 * Fintype.card V)
    (hcritical : ∀ v w, G.Adj v w → ∃ J, Tree G label J Finset.univ ∧ v ∈ J ∧ w ∈ J) :
    BipartiteModel M := by
  have hedge (v w : V) : G.Adj v w ↔ M.partner (B.index v) = B.index w := by
    constructor
    · intro h
      obtain ⟨J, N, hv, hw⟩ := hcritical v w h
      exact B.edge_in_imc_opposite hno d hdegree hbudget N hv hw h
    · exact B.opposite_complete v w
  refine ⟨B.index, ?_, hedge⟩
  intro v i
  rw [hedge, B.index_on_matching]
  constructor
  · intro h
    have he := congrArg M.partner h
    simpa only [M.partner_involutive] using he.symm
  · intro h
    exact congrArg M.partner h.symm

/-- The uniform r≥5 structure adapter. Its only graph-theoretic input beyond
the host hypotheses is critical-edge containment, supplied separately from
edge minimality. It assumes no cells, partition, or replacement configurations. -/
theorem Tree.bipartiteModel_of_edges_in_imcs {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} (M : Tree G label I Finset.univ) [Nonempty ι]
    (hno : ¬ HasFull G label) (n d : ℕ) (hr : 5 ≤ Fintype.card ι)
    (hparts : ∀ i, (fiber label i).card = n) (hdegree : ∀ v, degree G v ≤ d)
    (hdeg : (2 * (Fintype.card ι : ℝ) - 4) * d < ((Fintype.card ι : ℝ) - 1) * n)
    (hcritical : ∀ v w, G.Adj v w → ∃ J, Tree G label J Finset.univ ∧ v ∈ J ∧ w ∈ J) :
    Nonempty (BipartiteModel M) := by
  have hdef := M.total_cell_deficit_lt hno n d hr hparts hdegree hdeg
  obtain ⟨B⟩ := M.exists_expanded_partition hno d hdegree hdef
  have hbound := JSP896.structure_budget (by exact_mod_cast hr) (Nat.cast_nonneg d) hdeg
  have hI : (I.card : ℝ) + 2 = 2 * (Fintype.card ι : ℝ) := by exact_mod_cast M.full_card
  have hV : (Fintype.card V : ℝ) = (Fintype.card ι : ℝ) * n := by
    exact_mod_cast equal_parts_card label n hparts
  have hbudget : (2 * (I.card : ℝ) - 1) * d < 2 * Fintype.card V := by
    have hIeq : (I.card : ℝ) = 2 * (Fintype.card ι : ℝ) - 2 := by linarith
    rw [hIeq, hV]
    nlinarith
  exact ⟨B.to_bipartiteModel hno d hdegree hbudget hcritical⟩

end JSP896.MatchingConfiguration
