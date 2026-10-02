import JSP896.OddComponentsOrientation

/-!
# Centroid bounds for the constructed parent orientation

Parent reachability follows the distance gradient of the actual class tree.
The distance identities below put all descendants of a non-root class in one
of the root's centroid branches.  No descendant-size or path-containment
premise is added to `RootOrientation`.  Source only; no compiler has been run.
-/

namespace JSP896.MatchingConfiguration.RootOrientation

open OddComponents.Directed

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]
variable {G : SimpleGraph V} {label : V → ι} {I : Finset V}
    {M : Tree G label I Finset.univ} {root : ι} (O : RootOrientation M root)

theorem parent_adj {a b : ι} (hab : O.Parent a b) :
    (FeasiblePair.classGraph G label I).Adj a b := by
  have hadj : G.Adj (O.white b).1 (O.black b).1 :=
    (M.partner_adj (O.black b)).symm
  have hne := M.partite hadj
  rw [hab.2, O.color b hab.1] at hne
  exact ⟨hne, (O.white b).1, (O.white b).2,
    (O.black b).1, (O.black b).2, hadj, hab.2, O.color b hab.1⟩

/-- Every parent edge increases distance from the root by exactly one. -/
theorem parent_dist_add_one {a b : ι} (hab : O.Parent a b) :
    (FeasiblePair.classGraph G label I).dist b root =
      (FeasiblePair.classGraph G label I).dist a root + 1 := by
  let K := FeasiblePair.classGraph G label I
  have hdown : K.dist a root < K.dist b root := by
    have h := O.downhill b hab.1
    change K.dist (label (O.white b).1) root < K.dist b root at h
    rw [hab.2] at h
    exact h
  have hadj : K.Adj b a := (O.parent_adj hab).symm
  have hedge : K.dist b a = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
  have hle := hadj.reachable.dist_triangle_left root
  rw [hedge] at hle
  change K.dist b root = K.dist a root + 1
  omega

/-- A directed parent walk has exactly its endpoint distance as its length:
the root-distance increments rule out detours. -/
theorem parent_reach_dist {a b : ι} (hab : Reach O.Parent a b) :
    (FeasiblePair.classGraph G label I).dist b root =
      (FeasiblePair.classGraph G label I).dist a root +
        (FeasiblePair.classGraph G label I).dist a b := by
  let K := FeasiblePair.classGraph G label I
  change K.dist b root = K.dist a root + K.dist a b
  induction hab with
  | refl a => simp
  | @head a d b had hdb ih =>
    have hstep : K.dist d root = K.dist a root + 1 :=
      O.parent_dist_add_one had
    have hadj : K.Adj a d := O.parent_adj had
    have hedge : K.dist a d = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
    have hforward : K.dist a b ≤ 1 + K.dist d b := by
      have h := hadj.reachable.dist_triangle_left b
      simpa only [hedge] using h
    have hback : K.dist b root ≤ K.dist a b + K.dist a root := by
      calc
        K.dist b root ≤ K.dist b a + K.dist a root :=
          (M.connected b (Finset.mem_univ _) a (Finset.mem_univ _)).dist_triangle_left root
        _ = K.dist a b + K.dist a root := by
          rw [SimpleGraph.dist_comm (u := b) (v := a)]
    omega

/-- All parent-descendants of a non-root class lie in one root branch. -/
theorem parent_descendants_subset_branch {c : ι} (hc : c ≠ root) :
    ∃ child, (FeasiblePair.classGraph G label I).Adj root child ∧
      future O.Parent c ⊆
        branch (FeasiblePair.classGraph G label I) Finset.univ root child := by
  classical
  let K := FeasiblePair.classGraph G label I
  obtain ⟨child, hedge, hchildc⟩ := (O.parent_reachable c).first hc.symm
  refine ⟨child, O.parent_adj hedge, ?_⟩
  intro x hx
  have hcx : Reach O.Parent c x := (mem_future _ _ _).mp hx
  have hchildx := O.parent_reach_dist (hchildc.trans hcx)
  have hchildroot : K.dist child root = 1 := by
    have h := O.parent_dist_add_one hedge
    simpa only [SimpleGraph.dist_self, Nat.zero_add] using h
  change K.dist x root = K.dist child root + K.dist child x at hchildx
  rw [hchildroot, SimpleGraph.dist_comm (u := child) (v := x)] at hchildx
  apply (mem_branch K Finset.univ root child x).mpr
  exact ⟨Finset.mem_univ _, by omega⟩

/-- The metric centroid bound applies to every non-root parent-descendant set. -/
theorem parent_descendants_card_le {t : ℕ}
    (hcentroid : ∀ child, (FeasiblePair.classGraph G label I).Adj root child →
      (branch (FeasiblePair.classGraph G label I) Finset.univ root child).card ≤ t)
    {c : ι} (hc : c ≠ root) :
    (future O.Parent c).card ≤ t := by
  obtain ⟨child, hadj, hsub⟩ := O.parent_descendants_subset_branch hc
  exact (Finset.card_le_card hsub).trans (hcentroid child hadj)

end JSP896.MatchingConfiguration.RootOrientation
