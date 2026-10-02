import JSP896.DominationCertificate
import JSP896.FiniteGraphCounting

/-!
# A genuine independent-transversal theorem for paired deficit budgets

The input graph has actual finite nonempty colour fibres. The hypotheses are
only adjacency exclusions and numerical vertex-degree/fibre-size bounds. The
dominating certificate and its multiplicity bound are constructed by the proved
source chain, rather than supplied as existence hypotheses.
-/

open scoped BigOperators

namespace JSP896.PairedDeficit

open FiniteTransversal FeasiblePair FiniteGraphCounting

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]

theorem hasFull_of_paired_deficit (P : Pairing ι) (G : SimpleGraph V) (label : V → ι)
    (hpart : ∀ ⦃v w⦄, G.Adj v w → label v ≠ label w)
    (hopposite : ∀ ⦃v w⦄, G.Adj v w → label w ≠ P.partner (label v))
    (hsurj : ∀ i, ∃ v, label v = i) (δ ρ : ι → ℝ) (d : ℝ)
    (hδ : ∀ i, 0 ≤ δ i) (hρ : ∀ i, 0 ≤ ρ i)
    (hdeficit : (∑ i, δ i) < d) (hremoved : (∑ i, ρ i) ≤ d)
    (hsize : ∀ i, d - δ i - ρ i ≤ (fiber label i).card)
    (hdegree : ∀ v, (FiniteGraphCounting.degree G v : ℝ) ≤ δ (P.partner (label v))) :
    HasFull G label := by
  classical
  by_contra hno
  obtain ⟨J, T, hF, hJ, hdom⟩ := exists_feasible_dominating G label hpart hsurj hno
  let S := J.image label
  let t := certificateMultiplicity J label
  have hs : 2 ≤ S.card := hF.two_le_active_card hJ hpart
  have hlabels : ∀ v ∈ J, label v ∈ S := fun v hv => Finset.mem_image.mpr ⟨v, hv, rfl⟩
  have ht : MultiplicityBound P S t := multiplicityBound_of_faithful_edges P G J S label
    hs hlabels hpart hopposite hF.nonisolated hF.faithful
  have hρS : (∑ i ∈ S, ρ i) ≤ d := by
    calc
      _ ≤ ∑ i, ρ i := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun i _ _ => hρ i)
      _ ≤ d := hremoved
  have hsizeS : (S.card : ℝ) * d - (∑ i ∈ S, δ i) - (∑ i ∈ S, ρ i) ≤
      ((activeVertices label S).card : ℝ) := by
    have h : (∑ i ∈ S, (d - δ i - ρ i)) ≤
        ∑ i ∈ S, ((fiber label i).card : ℝ) :=
      Finset.sum_le_sum (fun i hi => hsize i)
    have hcards : (∑ i ∈ S, ((fiber label i).card : ℝ)) =
        ((activeVertices label S).card : ℝ) := by
      exact_mod_cast sum_fiber_card label S
    rw [hcards] at h
    simpa only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] using h
  have hdomNat := dominated_card_le_sum_degree G (activeVertices label S) J
    (fun v hv => hdom v ((mem_activeVertices label S v).mp hv))
  have hdomReal : ((activeVertices label S).card : ℝ) ≤
      ∑ v ∈ J, (FiniteGraphCounting.degree G v : ℝ) := by
    exact_mod_cast hdomNat
  have hsum : (∑ v ∈ J, (FiniteGraphCounting.degree G v : ℝ)) ≤
      ∑ i ∈ S, (t i : ℝ) * δ (P.partner i) := by
    calc
      _ ≤ ∑ v ∈ J, δ (P.partner (label v)) :=
        Finset.sum_le_sum (fun v hv => hdegree v)
      _ = _ := sum_by_label J S label (fun i => δ (P.partner i)) hlabels
  have hcover : (S.card : ℝ) * d - (∑ i, if i ∈ S then δ i else 0) -
      (∑ i ∈ S, ρ i) ≤
      ∑ i, if i ∈ S then (t i : ℝ) * δ (P.partner i) else 0 := by
    rw [indicator_sum, indicator_sum]
    exact hsizeS.trans (hdomReal.trans hsum)
  exact no_dominating_certificate P S t δ d (∑ i ∈ S, ρ i)
    hδ hs ht hdeficit hρS hcover

end JSP896.PairedDeficit
