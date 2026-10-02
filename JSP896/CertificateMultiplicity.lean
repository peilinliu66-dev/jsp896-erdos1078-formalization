import JSP896.PairedDeficit
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Order

/-!
# Actual vertex fibres imply the paired certificate multiplicity bound

A full feasible-pair certificate must provide nonisolated vertices and faithful
edges in its class multigraph. The tree property implies that distinct edges
cannot give parallel class edges. This module uses that precise faithfulness
property to inject each vertex fibre into allowable neighbouring classes.

The feasible-pair existence theorem itself remains an implementation obligation.
-/

namespace JSP896.PairedDeficit

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

def certificateMultiplicity (J : Finset V) (label : V → ι) (i : ι) : ℕ :=
  (J.filter fun v => label v = i).card

/-- No two ordered certificate edges give the same ordered pair of classes.
This is a literal property of edges, not a prescribed multiplicity inequality. -/
def FaithfulClassEdges (G : SimpleGraph V) (J : Finset V) (label : V → ι) : Prop :=
  ∀ v ∈ J, ∀ w ∈ J, ∀ v' ∈ J, ∀ w' ∈ J,
    G.Adj v w → G.Adj v' w' → label v = label v' → label w = label w' →
      v = v' ∧ w = w'

theorem fibre_card_le_erase_partner (P : Pairing ι) (G : SimpleGraph V)
    (J : Finset V) (S : Finset ι) (label : V → ι)
    (hlabels : ∀ v ∈ J, label v ∈ S)
    (hpartite : ∀ ⦃v w⦄, G.Adj v w → label v ≠ label w)
    (hopposite : ∀ ⦃v w⦄, G.Adj v w → label w ≠ P.partner (label v))
    (hnonisolated : ∀ v ∈ J, ∃ w ∈ J, G.Adj v w)
    (hfaithful : FaithfulClassEdges G J label) (i : ι) :
    certificateMultiplicity J label i ≤ ((S.erase i).erase (P.partner i)).card := by
  classical
  let F := J.filter fun v => label v = i
  let allowed := (S.erase i).erase (P.partner i)
  let nb : {v // v ∈ F} → V := fun v =>
    Classical.choose (hnonisolated v.1 (Finset.mem_filter.mp v.2).1)
  have hnb (v : {v // v ∈ F}) : nb v ∈ J ∧ G.Adj v.1 (nb v) :=
    Classical.choose_spec (hnonisolated v.1 (Finset.mem_filter.mp v.2).1)
  let f : {v // v ∈ F} → {j // j ∈ allowed} := fun v => ⟨label (nb v), by
    have hv : label v.1 = i := (Finset.mem_filter.mp v.2).2
    have hne : label (nb v) ≠ i := by
      intro h
      exact hpartite (hnb v).2 (hv.trans h.symm)
    have hpo : label (nb v) ≠ P.partner i := by
      simpa only [hv] using hopposite (hnb v).2
    exact Finset.mem_erase.mpr ⟨hpo,
      Finset.mem_erase.mpr ⟨hne, hlabels (nb v) (hnb v).1⟩⟩⟩
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    have hv := Finset.mem_filter.mp v.2
    have hw := Finset.mem_filter.mp w.2
    have hlabel : label v.1 = label w.1 := hv.2.trans hw.2.symm
    have hnbLabel : label (nb v) = label (nb w) := congrArg Subtype.val h
    exact (hfaithful v.1 hv.1 (nb v) (hnb v).1 w.1 hw.1 (nb w) (hnb w).1
      (hnb v).2 (hnb w).2 hlabel hnbLabel).1
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, F, allowed, certificateMultiplicity] using hcard

theorem multiplicityBound_of_faithful_edges (P : Pairing ι) (G : SimpleGraph V)
    (J : Finset V) (S : Finset ι) (label : V → ι) (hs : 2 ≤ S.card)
    (hlabels : ∀ v ∈ J, label v ∈ S)
    (hpartite : ∀ ⦃v w⦄, G.Adj v w → label v ≠ label w)
    (hopposite : ∀ ⦃v w⦄, G.Adj v w → label w ≠ P.partner (label v))
    (hnonisolated : ∀ v ∈ J, ∃ w ∈ J, G.Adj v w)
    (hfaithful : FaithfulClassEdges G J label) :
    MultiplicityBound P S (certificateMultiplicity J label) := by
  intro i hi
  have h := fibre_card_le_erase_partner P G J S label hlabels hpartite hopposite
    hnonisolated hfaithful i
  have hfirst : (S.erase i).card = S.card - 1 := Finset.card_erase_of_mem hi
  by_cases hp : P.partner i ∈ S
  · have hmem : P.partner i ∈ S.erase i :=
      Finset.mem_erase.mpr ⟨P.fixedPointFree i, hp⟩
    rw [Finset.card_erase_of_mem hmem, hfirst] at h
    have h' : certificateMultiplicity J label i ≤ S.card - 2 := by omega
    have hr := (Nat.cast_le (α := ℝ)).mpr h'
    rw [Nat.cast_sub hs] at hr
    simp only [if_pos hp]
    norm_num at hr ⊢
    linarith
  · have hnot : P.partner i ∉ S.erase i := by
      intro hmem
      exact hp (Finset.mem_erase.mp hmem).2
    rw [Finset.erase_eq_of_notMem hnot, hfirst] at h
    have hs1 : 1 ≤ S.card := by omega
    have hr := (Nat.cast_le (α := ℝ)).mpr h
    rw [Nat.cast_sub hs1] at hr
    simpa only [if_neg hp, sub_zero, Nat.cast_one] using hr

end JSP896.PairedDeficit
