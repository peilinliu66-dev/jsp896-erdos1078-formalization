import JSP896.FaithfulExtension

/-! Assembly of the actual star extension, including local minimality. -/

namespace JSP896.FeasiblePair

open FiniteTransversal

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]

theorem feasible_attach {G : SimpleGraph V} {label : V → ι} {I T U : Finset V}
    (hF : Feasible G label I T) (hU : Compatible G label I T U)
    (hpart : ∀ ⦃x y⦄, G.Adj x y → label x ≠ label y)
    (c : V) (havoid : ∀ v ∈ I, ¬ G.Adj c v)
    (hclass : label c ∈ I.image label ∨ label c ∉ T.image label)
    (hwhere : I = ∅ ∨ label c ∈ I.image label)
    (hmin : ∀ U', Compatible G label I T U' →
      (star G U c).card ≤ (star G U' c).card) :
    Feasible G label (I ∪ star G U c) U := by
  classical
  have hcenters := extended_centers hF hU c havoid hclass
  have hcU := new_center_not_mem_compatible hF hU c havoid hclass
  have hcI := hF.undominated_not_mem havoid
  have htree := extension_classTree hF hU hpart c havoid hwhere
  have hOldCenter (z : V) (hz : z ∈ I \ T) : z ∈ (I ∪ star G U c) \ U := by
    rw [hcenters]
    exact Finset.mem_insert_of_mem hz
  have hcCenter : c ∈ (I ∪ star G U c) \ U := by
    rw [hcenters]
    exact Finset.mem_insert_self _ _
  have hOldDisjoint {U' : Finset V} (h : Disjoint U' ((I ∪ star G U c) \ U)) :
      Disjoint U' (I \ T) := by
    apply h.mono_right
    intro z hz
    exact hOldCenter z hz
  have hActiveU (u : V) (hu : u ∈ U) (ha : label u ∈ I.image label) : u ∈ I :=
    active_T_vertex_mem_I hF (compatible_vertex_on_active_mem_T hF hU hu ha) ha
  refine ⟨Compatible.maximum hF hU, ?_, ?_, ?_, ?_, ?_, htree.acyclic,
    htree.connected, extension_faithful hF hU hpart c havoid, ?_⟩
  · ext i
    constructor
    · intro hi
      obtain ⟨v, hv, hvi⟩ := Finset.mem_image.mp hi
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_image.mpr ⟨v, (Finset.mem_inter.mp hv).1, hvi⟩,
         Finset.mem_image.mpr ⟨v, (Finset.mem_inter.mp hv).2, hvi⟩⟩
    · intro hi
      obtain ⟨v, hv, hvi⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hi).1
      obtain ⟨u, hu, hui⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hi).2
      have huNew : u ∈ I ∪ star G U c := by
        rcases Finset.mem_union.mp hv with hvI | hvStar
        · apply Finset.mem_union_left
          apply hActiveU u hu
          exact Finset.mem_image.mpr ⟨v, hvI, hvi.trans hui.symm⟩
        · rcases (mem_star G U c v).mp hvStar with rfl | hvLeaf
          · rcases hclass with ha | hm
            · apply Finset.mem_union_left
              apply hActiveU u hu
              rw [hui, ← hvi]
              exact ha
            · apply False.elim
              apply hm
              rw [← hU.colors]
              exact Finset.mem_image.mpr ⟨u, hu, hui.trans hvi.symm⟩
          · have huv : u = v := hU.partial.2 u hu v hvLeaf.1 (hui.trans hvi.symm)
            exact huv.symm ▸ Finset.mem_union_right I hvStar
      exact Finset.mem_image.mpr ⟨u, Finset.mem_inter.mpr ⟨huNew, hu⟩, hui⟩
  · intro x hx y hy
    rw [hcenters] at hx hy
    rcases Finset.mem_insert.mp hx with heq | hx
    · subst x
      rcases Finset.mem_insert.mp hy with heq | hy
      · subst y
        exact G.loopless.irrefl c
      · exact havoid y (Finset.mem_sdiff.mp hy).1
    · rcases Finset.mem_insert.mp hy with heq | hy
      · subst y
        intro h
        exact havoid x (Finset.mem_sdiff.mp hx).1 (G.adj_symm h)
      · exact hF.centersIndependent x hx y hy
  · intro z hz
    rw [hcenters] at hz
    rcases Finset.mem_insert.mp hz with heq | hz
    · subst z
      obtain ⟨v, hvU, hcv⟩ := undominated_extension_has_leaf hF hU c havoid hclass
      exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_union_right _
        ((mem_star G U c v).mpr (Or.inr ⟨hvU, hcv⟩)), hvU⟩, hcv⟩
    · obtain ⟨v, hv, hzv⟩ := hF.centersHaveLeaf z hz
      exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_union_left _
        (Finset.mem_inter.mp hv).1, leaf_mem_of_compatible hF hU hv⟩, hzv⟩
  · intro z hz v hv hzv
    rw [hcenters] at hz
    rcases Finset.mem_insert.mp hz with heq | hz
    · subst z
      exact Finset.mem_union_right _ ((mem_star G U c v).mpr (Or.inr ⟨hv, hzv⟩))
    · exact Finset.mem_union_left _ (compatible_center_neighbors_mem_I hF hU hz hv hzv)
  · intro v hv
    have hvU := (Finset.mem_inter.mp hv).2
    have hvNew := (Finset.mem_inter.mp hv).1
    by_cases hvI : v ∈ I
    · have hvT := compatible_vertex_on_active_mem_T hF hU hvU
        (Finset.mem_image.mpr ⟨v, hvI, rfl⟩)
      obtain ⟨z, hz, huniq⟩ := hF.leavesUnique v (Finset.mem_inter.mpr ⟨hvI, hvT⟩)
      refine ⟨z, ⟨hOldCenter z hz.1, hz.2⟩, ?_⟩
      intro z' hz'
      have hzmem := hz'.1
      rw [hcenters] at hzmem
      rcases Finset.mem_insert.mp hzmem with heq | hzmem
      · subst z'
        exact False.elim (havoid v hvI hz'.2)
      · exact huniq z' ⟨hzmem, hz'.2⟩
    · have hvStar : v ∈ star G U c := (Finset.mem_union.mp hvNew).resolve_left hvI
      have hcv : G.Adj c v := by
        rcases (mem_star G U c v).mp hvStar with rfl | hvL
        · exact False.elim (hcU hvU)
        · exact hvL.2
      refine ⟨c, ⟨hcCenter, hcv⟩, ?_⟩
      intro z hz
      have hzmem := hz.1
      rw [hcenters] at hzmem
      rcases Finset.mem_insert.mp hzmem with rfl | hzmem
      · rfl
      · exact False.elim (old_avoids_new_star hF hU c havoid
          (Finset.mem_sdiff.mp hzmem).1 hvStar hz.2)
  · intro z hz U' hPartial hColors hDis hStars
    have hColorsOld : U'.image label = T.image label := hColors.trans hU.colors
    have hDisOld := hOldDisjoint hDis
    rw [hcenters] at hz
    rcases Finset.mem_insert.mp hz with heq | hz
    · subst z
      apply hmin U'
      refine ⟨hPartial, hColorsOld, hDisOld, ?_⟩
      intro z hz
      have hzc : z ≠ c := by
        intro h
        exact hcI (h ▸ (Finset.mem_sdiff.mp hz).1)
      exact (hStars z (hOldCenter z hz) hzc).trans (hU.stars z hz)
    · rw [hU.stars z hz]
      apply hF.locallyMinimal z hz U' hPartial hColorsOld hDisOld
      intro z' hz' hne
      exact (hStars z' (hOldCenter z' hz') hne).trans (hU.stars z' hz')

theorem exists_feasible_extension {G : SimpleGraph V} {label : V → ι} {I T : Finset V}
    (hF : Feasible G label I T)
    (hpart : ∀ ⦃x y⦄, G.Adj x y → label x ≠ label y)
    (c : V) (havoid : ∀ v ∈ I, ¬ G.Adj c v)
    (hclass : label c ∈ I.image label ∨ label c ∉ T.image label)
    (hwhere : I = ∅ ∨ label c ∈ I.image label) :
    ∃ I' T', Feasible G label I' T' ∧ I ⊆ I' ∧ I.card < I'.card ∧
      Compatible G label I T T' := by
  classical
  obtain ⟨U, hU, hmin⟩ := exists_minimum_compatible_star hF c
  refine ⟨I ∪ star G U c, U, feasible_attach hF hU hpart c havoid hclass hwhere hmin,
    Finset.subset_union_left, ?_, hU⟩
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.subset_union_left, ?_⟩
  intro heq
  have hcNew : c ∈ I ∪ star G U c :=
    Finset.mem_union_right _ ((mem_star G U c c).mpr (Or.inl rfl))
  rw [← heq] at hcNew
  exact hF.undominated_not_mem havoid hcNew

end JSP896.FeasiblePair
