import JSP896.Statement
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Order

/-! Exact finite degree accounting for the cross-part complement. -/

namespace JSP896

def crossNeighbors {r n : ℕ} (v : Vertex r n) : Finset (Vertex r n) :=
  (Finset.univ.erase v.1).product Finset.univ

@[simp] theorem mem_crossNeighbors {r n : ℕ} (v w : Vertex r n) :
    w ∈ crossNeighbors v ↔ v.1 ≠ w.1 := by
  simp [crossNeighbors, ne_comm]

theorem card_crossNeighbors {r n : ℕ} (v : Vertex r n) :
    (crossNeighbors v).card = (r - 1) * n := by
  simp [crossNeighbors]

theorem neighbors_disjoint_complement {r n : ℕ}
    (G : SimpleGraph (Vertex r n)) (v : Vertex r n) :
    Disjoint (neighbors G v) (neighbors (crossComplement G) v) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hw hw'
  have h := (mem_neighbors G v w).mp hw
  have h' := (mem_neighbors (crossComplement G) v w).mp hw'
  exact h'.2 h

theorem neighbors_union_complement {r n : ℕ}
    (G : SimpleGraph (Vertex r n)) (hpart : IsPartite G) (v : Vertex r n) :
    neighbors G v ∪ neighbors (crossComplement G) v = crossNeighbors v := by
  classical
  ext w
  simp only [Finset.mem_union, mem_neighbors, mem_crossNeighbors]
  change (G.Adj v w ∨ (v.1 ≠ w.1 ∧ ¬ G.Adj v w)) ↔ v.1 ≠ w.1
  constructor
  · rintro (h | h)
    · exact hpart h
    · exact h.1
  · intro hne
    by_cases h : G.Adj v w
    · exact Or.inl h
    · exact Or.inr ⟨hne, h⟩

theorem degree_add_complement {r n : ℕ}
    (G : SimpleGraph (Vertex r n)) (hpart : IsPartite G) (v : Vertex r n) :
    degree G v + degree (crossComplement G) v = (r - 1) * n := by
  classical
  have h := congrArg Finset.card (neighbors_union_complement G hpart v)
  rw [Finset.card_union_of_disjoint (neighbors_disjoint_complement G v)] at h
  simpa only [degree, card_crossNeighbors] using h

theorem degree_le_crossPartCapacity {r n : ℕ}
    (G : SimpleGraph (Vertex r n)) (hpart : IsPartite G) (v : Vertex r n) :
    degree G v ≤ (r - 1) * n := by
  have h := degree_add_complement G hpart v
  omega

/-- Integer strictness, with the natural-subtraction side condition explicit. -/
theorem complement_degree_lt_iff {r n D : ℕ}
    (G : SimpleGraph (Vertex r n)) (hpart : IsPartite G) (v : Vertex r n)
    (hD : D ≤ (r - 1) * n) :
    degree (crossComplement G) v < D ↔ (r - 1) * n - D < degree G v := by
  have h := degree_add_complement G hpart v
  omega

theorem complement_degree_le_iff {r n D : ℕ}
    (G : SimpleGraph (Vertex r n)) (hpart : IsPartite G) (v : Vertex r n)
    (hD : D ≤ (r - 1) * n) :
    degree (crossComplement G) v ≤ D ↔ (r - 1) * n - D ≤ degree G v := by
  have h := degree_add_complement G hpart v
  omega

end JSP896
