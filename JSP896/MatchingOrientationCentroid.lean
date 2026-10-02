import JSP896.MatchingOrientation
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max

/-!
# A genuine centroid selected by minimum total tree distance

Moving across an edge changes every distance by exactly one.  If B vertices
are on the far side, the distance sum changes by |S|-2B.  A minimum therefore
has B≤t on each branch when |S|=2t+1.  No centroid-existence hypothesis is used.
The branch is expressed by its exact metric cut.  Pinned execution records are in VERIFICATION.md.
-/

namespace JSP896.MatchingConfiguration

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def distanceScore (K : SimpleGraph ι) (S : Finset ι) (root : ι) : ℕ :=
  ∑ c ∈ S, K.dist c root

noncomputable def branch (K : SimpleGraph ι) (S : Finset ι) (root child : ι) : Finset ι := by
  classical
  exact S.filter (fun c => K.dist c child < K.dist c root)

@[simp] theorem mem_branch (K : SimpleGraph ι) (S : Finset ι) (root child c : ι) :
    c ∈ branch K S root child ↔ c ∈ S ∧ K.dist c child < K.dist c root := by
  classical
  simp [branch]

/-- Along an edge of a forest, distances from a reachable vertex differ by
exactly one.  This local proof uses unique paths rather than a separately
named distance-step theorem. -/
theorem tree_dist_step (K : SimpleGraph ι) (hacyclic : K.IsAcyclic)
    (c : ι) {root child : ι} (hedge : K.Adj root child)
    (hreach : K.Reachable c root) :
    K.dist c root = K.dist c child + 1 ∨
      K.dist c child = K.dist c root + 1 := by
  classical
  obtain ⟨p, hp, hplength⟩ := hreach.exists_path_of_dist
  obtain ⟨q, hq, hqlength⟩ :=
    (hreach.trans hedge.reachable).exists_path_of_dist
  by_cases hroot : root ∈ q.support
  · have heq : q = p.concat hedge := hacyclic.path_concat hp hq hedge hroot
    have hlength := congrArg SimpleGraph.Walk.length heq
    simp only [SimpleGraph.Walk.length_concat] at hlength
    rw [hplength, hqlength] at hlength
    exact Or.inr hlength
  · have hchild : child ∈ p.support :=
      hacyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hp hq hedge hroot
    have heq : p = q.concat hedge.symm :=
      hacyclic.path_concat hq hp hedge.symm hchild
    have hlength := congrArg SimpleGraph.Walk.length heq
    simp only [SimpleGraph.Walk.length_concat] at hlength
    rw [hplength, hqlength] at hlength
    exact Or.inl hlength

theorem distanceScore_edge_balance (K : SimpleGraph ι) (S : Finset ι)
    (hacyclic : K.IsAcyclic)
    (hconn : ∀ i ∈ S, ∀ j ∈ S, K.Reachable i j)
    {root child : ι} (hroot : root ∈ S) (_hchild : child ∈ S)
    (hedge : K.Adj root child) :
    distanceScore K S child + 2 * (branch K S root child).card =
      distanceScore K S root + S.card := by
  classical
  have hpoint : ∀ c ∈ S,
      K.dist c child + 2 * (if K.dist c child < K.dist c root then 1 else 0) =
        K.dist c root + 1 := by
    intro c hc
    have hstep := tree_dist_step K hacyclic c hedge
      (hconn c hc root hroot)
    split_ifs with hlt <;> rcases hstep with hstep | hstep <;> omega
  have hcount : (∑ c ∈ S, if K.dist c child < K.dist c root then 1 else 0) =
      (branch K S root child).card := by
    simp only [branch, Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    distanceScore K S child + 2 * (branch K S root child).card =
        ∑ c ∈ S, (K.dist c child +
          2 * (if K.dist c child < K.dist c root then 1 else 0)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcount]
      rfl
    _ = ∑ c ∈ S, (K.dist c root + 1) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact hpoint c hc
    _ = distanceScore K S root + S.card := by
      simp [distanceScore, Finset.sum_add_distrib]

/-- A centroid with an explicit bound on every branch of its class tree. -/
theorem exists_centroid (K : SimpleGraph ι) (S : Finset ι) (t : ℕ)
    (hcard : S.card = 2 * t + 1) (hacyclic : K.IsAcyclic)
    (hconn : ∀ i ∈ S, ∀ j ∈ S, K.Reachable i j) :
    ∃ root ∈ S, ∀ child ∈ S, K.Adj root child →
      (branch K S root child).card ≤ t := by
  classical
  have hnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨root, hroot, hmin⟩ := S.exists_min_image (distanceScore K S) hnonempty
  refine ⟨root, hroot, ?_⟩
  intro child hchild hedge
  have hscore := hmin child hchild
  have hbalance := distanceScore_edge_balance K S hacyclic hconn hroot hchild hedge
  omega

theorem Tree.exists_centroid {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {label : V → ι} {I : Finset V} {S : Finset ι}
    (M : Tree G label I S) (t : ℕ) (hcard : S.card = 2 * t + 1) :
    ∃ root ∈ S, ∀ child ∈ S, (FeasiblePair.classGraph G label I).Adj root child →
      (branch (FeasiblePair.classGraph G label I) S root child).card ≤ t :=
  JSP896.MatchingConfiguration.exists_centroid _ S t hcard M.acyclic M.connected

end JSP896.MatchingConfiguration
