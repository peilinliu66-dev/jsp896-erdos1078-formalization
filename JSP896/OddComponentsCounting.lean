import JSP896.MatchingOrientationCentroid
import JSP896.Statement
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Exact independence and small-class domination bounds for odd components

These are Facts 1 and the counting assertion of Fact 3 in the readable
Haxell--Szabó proof, expressed using actual graph vertices and neighborhoods.
They are prerequisites, not an assertion of the final switching theorem.
Pinned execution records are in VERIFICATION.md.
-/

namespace JSP896.MatchingConfiguration

open FiniteTransversal
open scoped BigOperators

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]

/-- Fact 1, in a form usable by both finite switches. -/
theorem BipartiteModel.neighborhood_switch_independent
    {G : SimpleGraph V} {label : V → ι} {I : Finset V} {S : Finset ι}
    {M : Tree G label I S} (B : BipartiteModel M)
    {P Z X U : Finset V} (hPI : P ⊆ I)
    (hP : ∀ v ∈ P, ∀ w ∈ P, ¬ G.Adj v w)
    (hZP : Z ⊆ P) (hXP : X ⊆ P) (hZX : Disjoint Z X)
    (hU : ∀ v ∈ U, ∃ z ∈ Z, G.Adj v z) :
    ∀ v ∈ U ∪ X, ∀ w ∈ U ∪ X, ¬ G.Adj v w := by
  classical
  have hUU : ∀ v ∈ U, ∀ w ∈ U, ¬ G.Adj v w := by
    intro v hv w hw hadj
    obtain ⟨z, hz, hvz⟩ := hU v hv
    obtain ⟨z', hz', hwz'⟩ := hU w hw
    let iz : IVertex I := ⟨z, hPI (hZP hz)⟩
    let iz' : IVertex I := ⟨z', hPI (hZP hz')⟩
    have hindex : iz = B.index v := (B.uniqueNeighbour v iz).mp hvz
    have hindex' : iz' = B.index w := (B.uniqueNeighbour w iz').mp hwz'
    have hpartners := (B.edge_iff v w).mp hadj
    rw [← hindex, ← hindex'] at hpartners
    exact hP z (hZP hz) z' (hZP hz')
      ((M.adj_iff_partner iz iz').mpr hpartners)
  have hUX : ∀ v ∈ U, ∀ w ∈ X, ¬ G.Adj v w := by
    intro v hv w hw hadj
    obtain ⟨z, hz, hvz⟩ := hU v hv
    let iz : IVertex I := ⟨z, hPI (hZP hz)⟩
    let iw : IVertex I := ⟨w, hPI (hXP hw)⟩
    have hindex : iz = B.index v := (B.uniqueNeighbour v iz).mp hvz
    have hindex' : iw = B.index v := (B.uniqueNeighbour v iw).mp hadj
    have hzw : z = w := congrArg Subtype.val (hindex.trans hindex'.symm)
    exact (Finset.disjoint_left.mp hZX) hz (hzw.symm ▸ hw)
  intro v hv w hw hadj
  rcases Finset.mem_union.mp hv with hv | hv <;>
    rcases Finset.mem_union.mp hw with hw | hw
  · exact hUU v hv w hw hadj
  · exact hUX v hv w hw hadj
  · exact hUX w hw v hv (G.adj_symm hadj)
  · exact hP v (hXP hv) w (hXP hw) hadj

end JSP896.MatchingConfiguration

namespace JSP896.OddComponents

open scoped BigOperators

/-- The odd threshold is strong enough for every nonempty collection of at
most t classes; no division or asymptotic rounding is involved. -/
theorem small_class_strict_bound {t n d s : ℕ}
    (ht : 0 < t) (hs : 0 < s) (hst : s ≤ t)
    (hthreshold : (2 * t - 1) * d < t * n) :
    (2 * s - 1) * d < s * n := by
  by_contra h
  have hcounter : s * n ≤ (2 * s - 1) * d := by omega
  have h1 := Nat.mul_lt_mul_of_pos_left hthreshold hs
  have h2 := Nat.mul_le_mul_left t hcounter
  have hgap := Nat.mul_le_mul_right d hst
  have htcoef : 2 * t - 1 + 1 = 2 * t := by omega
  have hscoef : 2 * s - 1 + 1 = 2 * s := by omega
  have heq1 : s * ((2 * t - 1) * d) + s * d = 2 * s * t * d := by
    calc
      s * ((2 * t - 1) * d) + s * d = s * ((2 * t - 1 + 1) * d) := by ring
      _ = 2 * s * t * d := by rw [htcoef]; ring
  have heq2 : t * ((2 * s - 1) * d) + t * d = 2 * s * t * d := by
    calc
      t * ((2 * s - 1) * d) + t * d = t * ((2 * s - 1 + 1) * d) := by ring
      _ = 2 * s * t * d := by rw [hscoef]; ring
  nlinarith

/-- Literal domination count: all vertices of L require at least |L|n
neighbor incidences, while D supplies at most |D|d. -/
theorem class_domination_card_bound {r n d : ℕ}
    (G : SimpleGraph (Vertex r n)) (hdegree : ∀ v, degree G v ≤ d)
    (L : Finset (Fin r)) (D : Finset (Vertex r n))
    (hdom : ∀ v : Vertex r n, v.1 ∈ L → ∃ w ∈ D, G.Adj v w) :
    L.card * n ≤ D.card * d := by
  classical
  have hsubset : L.product (Finset.univ : Finset (Fin n)) ⊆
      D.biUnion (neighbors G) := by
    intro v hv
    obtain ⟨w, hw, hvw⟩ := hdom v (Finset.mem_product.mp hv).1
    exact Finset.mem_biUnion.mpr ⟨w, hw, (mem_neighbors _ _ _).mpr (G.adj_symm hvw)⟩
  calc
    L.card * n = (L.product (Finset.univ : Finset (Fin n))).card := by simp
    _ ≤ (D.biUnion (neighbors G)).card := Finset.card_le_card hsubset
    _ ≤ ∑ w ∈ D, (neighbors G w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ D, d := by
      apply Finset.sum_le_sum
      intro w _hw
      exact hdegree w
    _ = D.card * d := by simp

/-- Fact 3: fewer than 2|L| actual vertices cannot dominate a nonempty
collection L of at most t classes. -/
theorem exists_undominated_in_small_classes {t n d : ℕ}
    (ht : 0 < t) (_hn : 0 < n)
    (hthreshold : (2 * t - 1) * d < t * n)
    (G : SimpleGraph (Vertex (2 * t + 1) n))
    (hdegree : ∀ v, degree G v ≤ d)
    (L : Finset (Fin (2 * t + 1))) (hL : L.Nonempty) (hLt : L.card ≤ t)
    (D : Finset (Vertex (2 * t + 1) n)) (hD : D.card < 2 * L.card) :
    ∃ v : Vertex (2 * t + 1) n, v.1 ∈ L ∧ ∀ w ∈ D, ¬ G.Adj v w := by
  classical
  by_contra hnone
  have hdom : ∀ v : Vertex (2 * t + 1) n, v.1 ∈ L → ∃ w ∈ D, G.Adj v w := by
    intro v hv
    by_contra havoid
    push_neg at havoid
    exact hnone ⟨v, hv, havoid⟩
  have hcount := class_domination_card_bound G hdegree L D hdom
  have hsmall := small_class_strict_bound ht (Finset.card_pos.mpr hL) hLt hthreshold
  have hDle : D.card ≤ 2 * L.card - 1 := by omega
  have hmul := Nat.mul_le_mul_right d hDle
  omega

end JSP896.OddComponents
