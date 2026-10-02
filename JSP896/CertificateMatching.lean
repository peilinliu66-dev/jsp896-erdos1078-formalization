import JSP896.CertificateSize
import JSP896.FiniteGraphCounting
import JSP896.MatchingTree
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith

/-! A feasible star forest either is an induced matching, or has at most
`2r-3` vertices. This is a statement about the literal host graph. -/

namespace JSP896.FeasiblePair

open FiniteTransversal

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]

theorem Feasible.matching_or_small {G : SimpleGraph V} {label : V → ι}
    {I T : Finset V} (hF : Feasible G label I T) (hno : ¬ HasFull G label) :
    (∀ v ∈ I, ∃! w, w ∈ I ∧ G.Adj v w) ∨ I.card + 3 ≤ 2 * Fintype.card ι := by
  classical
  let C := I \ T
  let L := I ∩ T
  let f : ↥C → ↥L := fun c =>
    ⟨Classical.choose (hF.centersHaveLeaf c.1 c.2),
      (Classical.choose_spec (hF.centersHaveLeaf c.1 c.2)).1⟩
  have hfadj (c : ↥C) : G.Adj c.1 (f c).1 :=
    (Classical.choose_spec (hF.centersHaveLeaf c.1 c.2)).2
  have hfinj : Function.Injective f := by
    intro c e h
    have heq : (f c).1 = (f e).1 := congrArg Subtype.val h
    obtain ⟨w, hw, hu⟩ := hF.leavesUnique (f c).1 (f c).2
    apply Subtype.ext
    exact (hu c.1 ⟨c.2, hfadj c⟩).trans
      (hu e.1 ⟨e.2, by simpa only [heq] using hfadj e⟩).symm
  have hcle : C.card ≤ L.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hfinj
  by_cases heq : C.card = L.card
  · left
    have hsurj : Function.Surjective f :=
      ((Fintype.bijective_iff_injective_and_card f).mpr
        ⟨hfinj, by simpa only [Fintype.card_coe] using heq⟩).2
    intro v hv
    by_cases hvT : v ∈ T
    · obtain ⟨w, hw, hu⟩ := hF.leavesUnique v (Finset.mem_inter.mpr ⟨hv, hvT⟩)
      refine ⟨w, ⟨(Finset.mem_sdiff.mp hw.1).1, G.adj_symm hw.2⟩, ?_⟩
      intro z hz
      have hzT : z ∉ T := fun h => hF.maximum.1.1 v hvT z h hz.2
      exact hu z ⟨Finset.mem_sdiff.mpr ⟨hz.1, hzT⟩, G.adj_symm hz.2⟩
    · let c : ↥C := ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvT⟩⟩
      refine ⟨(f c).1, ⟨(Finset.mem_inter.mp (f c).2).1, hfadj c⟩, ?_⟩
      intro z hz
      have hzT : z ∈ T := by
        by_contra h
        exact hF.centersIndependent v c.2 z (Finset.mem_sdiff.mpr ⟨hz.1, h⟩) hz.2
      let l : ↥L := ⟨z, Finset.mem_inter.mpr ⟨hz.1, hzT⟩⟩
      obtain ⟨e, he⟩ := hsurj l
      obtain ⟨w, hw, hu⟩ := hF.leavesUnique z l.2
      have hev : e = c := by
        apply Subtype.ext
        exact (hu e.1 ⟨e.2, by simpa only [he] using hfadj e⟩).trans
          (hu v ⟨c.2, hz.2⟩).symm
      have := congrArg Subtype.val he
      simpa only [hev] using this.symm
  · right
    have hlt : C.card < L.card := lt_of_le_of_ne hcle heq
    have hL : L.card ≤ T.card := Finset.card_le_card Finset.inter_subset_right
    have hT := hF.maximum.1.card_lt_of_no_full hno
    have hsplit : C.card + L.card = I.card := Finset.card_sdiff_add_card_inter I T
    omega

theorem Feasible.toMatchingTree {G : SimpleGraph V} {label : V → ι}
    {I T : Finset V} (hF : Feasible G label I T)
    (hpart : ∀ ⦃v w⦄, G.Adj v w → label v ≠ label w)
    (hall : I.image label = Finset.univ)
    (hmatch : ∀ v ∈ I, ∃! w, w ∈ I ∧ G.Adj v w) :
    MatchingConfiguration.Tree G label I Finset.univ where
  partite := hpart
  within := by simp
  matched := hmatch
  acyclic := hF.classAcyclic
  connected := by
    intro i hi j hj
    apply hF.classConnected i _ j _ <;> simpa only [hall] using (Finset.mem_univ _)
  faithful := hF.faithful

end JSP896.FeasiblePair
