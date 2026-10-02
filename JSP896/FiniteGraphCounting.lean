import JSP896.CertificateMultiplicity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Literal finite neighbourhood, domination and colour-fibre counting. -/

open scoped BigOperators

namespace JSP896.FiniteGraphCounting

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]

noncomputable def neighbors (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (G.Adj v)

noncomputable def degree (G : SimpleGraph V) (v : V) : ℕ := (neighbors G v).card

def fiber (label : V → ι) (i : ι) : Finset V := Finset.univ.filter fun v => label v = i

def activeVertices (label : V → ι) (S : Finset ι) : Finset V :=
  Finset.univ.filter fun v => label v ∈ S

@[simp] theorem mem_neighbors (G : SimpleGraph V) (v w : V) :
    w ∈ neighbors G v ↔ G.Adj v w := by
  classical
  simp [neighbors]

@[simp] theorem mem_fiber (label : V → ι) (i : ι) (v : V) :
    v ∈ fiber label i ↔ label v = i := by simp [fiber]

@[simp] theorem mem_activeVertices (label : V → ι) (S : Finset ι) (v : V) :
    v ∈ activeVertices label S ↔ label v ∈ S := by simp [activeVertices]

theorem dominated_card_le_sum_degree (G : SimpleGraph V) (A J : Finset V)
    (hdom : ∀ v ∈ A, ∃ w ∈ J, G.Adj w v) :
    A.card ≤ ∑ w ∈ J, degree G w := by
  classical
  have hsub : A ⊆ J.biUnion (neighbors G) := by
    intro v hv
    obtain ⟨w, hw, hwv⟩ := hdom v hv
    exact Finset.mem_biUnion.mpr ⟨w, hw, (mem_neighbors G w v).mpr hwv⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

theorem sum_fiber_card (label : V → ι) (S : Finset ι) :
    (∑ i ∈ S, (fiber label i).card) = (activeVertices label S).card := by
  exact Finset.sum_card_fiberwise_eq_card_filter Finset.univ S label

theorem sum_by_label (J : Finset V) (S : Finset ι) (label : V → ι) (f : ι → ℝ)
    (hlabel : ∀ v ∈ J, label v ∈ S) :
    (∑ v ∈ J, f (label v)) =
      ∑ i ∈ S, (PairedDeficit.certificateMultiplicity J label i : ℝ) * f i := by
  have h := Finset.sum_fiberwise_of_maps_to' hlabel f
  simpa only [Finset.sum_const, nsmul_eq_mul, PairedDeficit.certificateMultiplicity]
    using h.symm

theorem indicator_sum (S : Finset ι) (f : ι → ℝ) :
    (∑ i, if i ∈ S then f i else 0) = ∑ i ∈ S, f i := by
  rw [← Finset.sum_filter]
  simp

end JSP896.FiniteGraphCounting
