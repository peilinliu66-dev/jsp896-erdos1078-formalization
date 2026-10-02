import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Order

/-! Literal partial transversals and finite maximality, for arbitrary finite
nonempty-part partitions used both in the host graph and the auxiliary graph. -/

namespace JSP896.FiniteTransversal

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]

def Partial (G : SimpleGraph V) (label : V → ι) (T : Finset V) : Prop :=
  (∀ x ∈ T, ∀ y ∈ T, ¬ G.Adj x y) ∧
    ∀ x ∈ T, ∀ y ∈ T, label x = label y → x = y

def Full (G : SimpleGraph V) (label : V → ι) (T : Finset V) : Prop :=
  Partial G label T ∧ T.image label = Finset.univ

def HasFull (G : SimpleGraph V) (label : V → ι) : Prop :=
  ∃ T, Full G label T

def Maximum (G : SimpleGraph V) (label : V → ι) (T : Finset V) : Prop :=
  Partial G label T ∧ ∀ U, Partial G label U → U.card ≤ T.card

theorem partial_empty (G : SimpleGraph V) (label : V → ι) :
    Partial G label ∅ := by
  simp [Partial]

theorem Partial.subset {G : SimpleGraph V} {label : V → ι} {T U : Finset V}
    (hT : Partial G label T) (hUT : U ⊆ T) : Partial G label U := by
  constructor
  · intro x hx y hy
    exact hT.1 x (hUT hx) y (hUT hy)
  · intro x hx y hy hxy
    exact hT.2 x (hUT hx) y (hUT hy) hxy

theorem Partial.card_image {G : SimpleGraph V} {label : V → ι} {T : Finset V}
    (hT : Partial G label T) : (T.image label).card = T.card := by
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  exact hT.2 x hx y hy hxy

theorem exists_maximum (G : SimpleGraph V) (label : V → ι) :
    ∃ T, Maximum G label T := by
  classical
  let candidates := (Finset.univ : Finset V).powerset.filter (Partial G label)
  have hne : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, partial_empty]
  obtain ⟨T, hT, hmax⟩ := candidates.exists_max_image Finset.card hne
  refine ⟨T, (Finset.mem_filter.mp hT).2, ?_⟩
  intro U hU
  apply hmax U
  simp [candidates, hU]

theorem partial_insert {G : SimpleGraph V} {label : V → ι} {T : Finset V}
    (hT : Partial G label T) (x : V) (hmissing : label x ∉ T.image label)
    (havoids : ∀ y ∈ T, ¬ G.Adj x y) : Partial G label (insert x T) := by
  constructor
  · intro a ha b hb
    rcases Finset.mem_insert.mp ha with hax | ha
    · subst a
      rcases Finset.mem_insert.mp hb with hbx | hb
      · subst b
        exact G.loopless.irrefl x
      · exact havoids b hb
    · rcases Finset.mem_insert.mp hb with hbx | hb
      · subst b
        intro h
        exact havoids a ha (G.adj_symm h)
      · exact hT.1 a ha b hb
  · intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hax | ha
    · subst a
      rcases Finset.mem_insert.mp hb with hbx | hb
      · subst b
        rfl
      · exact False.elim (hmissing (Finset.mem_image.mpr ⟨b, hb, hab.symm⟩))
    · rcases Finset.mem_insert.mp hb with hbx | hb
      · subst b
        exact False.elim (hmissing (Finset.mem_image.mpr ⟨a, ha, hab⟩))
      · exact hT.2 a ha b hb hab

theorem Maximum.missing_vertex_has_neighbour {G : SimpleGraph V} {label : V → ι}
    {T : Finset V} (hT : Maximum G label T) (x : V)
    (hmissing : label x ∉ T.image label) : ∃ y ∈ T, G.Adj x y := by
  classical
  by_contra h
  have havoids : ∀ y ∈ T, ¬ G.Adj x y := by
    intro y hy hxy
    exact h ⟨y, hy, hxy⟩
  have hnew := partial_insert hT.1 x hmissing havoids
  have hcard := hT.2 (insert x T) hnew
  have hx : x ∉ T := by
    intro hx
    exact hmissing (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  rw [Finset.card_insert_of_notMem hx] at hcard
  omega

theorem Partial.card_lt_of_no_full {G : SimpleGraph V} {label : V → ι}
    {T : Finset V} (hT : Partial G label T) (hno : ¬ HasFull G label) :
    T.card < Fintype.card ι := by
  have hle : T.card ≤ Fintype.card ι := by
    rw [← hT.card_image]
    exact (Finset.card_le_card (Finset.subset_univ (T.image label))).trans_eq
      Finset.card_univ
  have hne : T.card ≠ Fintype.card ι := by
    intro heq
    have himage : T.image label = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      simpa only [Finset.card_univ, hT.card_image, heq] using
        (le_refl (Fintype.card ι))
    exact hno ⟨T, hT, himage⟩
  omega

theorem partial_swap {G : SimpleGraph V} {label : V → ι} {T : Finset V}
    (hT : Partial G label T) {u x : V} (hu : u ∈ T)
    (hcolor : label x = label u)
    (havoids : ∀ y ∈ T.erase u, ¬ G.Adj x y) :
    Partial G label (insert x (T.erase u)) := by
  have hsub : Partial G label (T.erase u) := hT.subset (Finset.erase_subset _ _)
  apply partial_insert hsub x ?_ havoids
  intro hmem
  obtain ⟨y, hy, hlabel⟩ := Finset.mem_image.mp hmem
  have hyu : y = u := hT.2 y (Finset.mem_erase.mp hy).2 u hu (hlabel.trans hcolor)
  exact (Finset.mem_erase.mp hy).1 hyu

theorem swap_colors {label : V → ι} {T : Finset V} {u x : V}
    (hu : u ∈ T) (hcolor : label x = label u) :
    (insert x (T.erase u)).image label = T.image label := by
  ext i
  constructor
  · intro hi
    obtain ⟨v, hv, hvi⟩ := Finset.mem_image.mp hi
    rcases Finset.mem_insert.mp hv with hv | hv
    · subst v
      exact Finset.mem_image.mpr ⟨u, hu, hcolor.symm.trans hvi⟩
    · exact Finset.mem_image.mpr ⟨v, (Finset.mem_erase.mp hv).2, hvi⟩
  · intro hi
    obtain ⟨v, hv, hvi⟩ := Finset.mem_image.mp hi
    by_cases hvu : v = u
    · subst v
      exact Finset.mem_image.mpr ⟨x, Finset.mem_insert_self _ _, hcolor.trans hvi⟩
    · exact Finset.mem_image.mpr ⟨v,
        Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hvu, hv⟩), hvi⟩

theorem Partial.card_eq_of_colors_eq {G : SimpleGraph V} {label : V → ι}
    {T U : Finset V} (hT : Partial G label T) (hU : Partial G label U)
    (hcolor : U.image label = T.image label) : U.card = T.card := by
  rw [← hU.card_image, hcolor, hT.card_image]

theorem Maximum.of_colors_eq {G : SimpleGraph V} {label : V → ι}
    {T U : Finset V} (hT : Maximum G label T) (hU : Partial G label U)
    (hcolor : U.image label = T.image label) : Maximum G label U := by
  refine ⟨hU, ?_⟩
  intro W hW
  rw [hT.1.card_eq_of_colors_eq hU hcolor]
  exact hT.2 W hW

end JSP896.FiniteTransversal
